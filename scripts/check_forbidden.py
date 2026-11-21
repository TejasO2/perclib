#!/usr/bin/env python3
"""Forbidden-construct scan of the whole library (D-29, D-34).

Usage: python3 scripts/check_forbidden.py [ROOT]      (default ROOT: PercLib)

Fails if any Lean file under ROOT, outside comments and string literals, uses a
construct that leaves a proof unchecked, adds an axiom, or can run code at
elaboration time: `sorry`, `admit`, `native_decide`, `axiom`, `by_elab`, `run_tac`,
`run_cmd`, `run_elab`, `#eval`, `elab`, `macro`, `syntax`, `initialize`, `unsafe`,
`implemented_by`, `extern`, `skipKernelTC` (however quoted), `addDecl`, `command_elab`,
`term_elab`, `tactic_elab`, or a `set_option` outside a short allowlist (D-35: no
`maxHeartbeats` and no `linter.*`). The tag attribute itself (`PercLib/Meta/Tag.lean`) is the one file
allowed to declare syntax and an initializer, and only those.

This is a second line behind the axiom audit and the kernel replay; it fails closed.
Standard library only.
"""
from __future__ import annotations

import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from check_proof_pr import code_without_literals  # noqa: E402

FORBIDDEN = set('sorry admit native_decide axiom axioms by_elab run_tac run_cmd run_elab '
                'elab elab_rules macro macro_rules syntax initialize builtin_initialize '
                'unsafe implemented_by extern skipKernelTC debug addDecl command_elab term_elab '
                'tactic_elab'.split())
# D-35: maxHeartbeats, synthInstance.maxHeartbeats and linter.* are not allowed; a real
# need is an audited exception added here with its reason.
ALLOWED_OPTIONS = re.compile(r'(maxRecDepth|backward\.isDefEq\.respectTransparency|'
                             r'pp\.[\w.]+)$')
EXEMPT = {'PercLib/Meta/Tag.lean': {'syntax', 'initialize'}}


def identifiers(code: str) -> list[str]:
    # «guillemet» quoting and dotted names are split into components, so
    # `«debug».skipKernelTC` and `set_option debug.skipKernelTC` are both caught.
    code = code.replace('«', ' ').replace('»', ' ')
    return re.findall(r'#?[A-Za-z_][A-Za-z0-9_!?\']*', code)


def check_file(rel: str, text: str) -> list[str]:
    try:
        code = code_without_literals(text)
    except ValueError as e:
        return [f'{rel}: cannot parse ({e})']
    problems = []
    found = set()
    for tok in identifiers(code):
        if tok in FORBIDDEN or tok == '#eval':
            found.add(tok)
    found -= EXEMPT.get(rel, set())
    if found:
        problems.append(f'{rel}: forbidden tokens {sorted(found)}')
    for m in re.finditer(r'set_option\s+([^\s]+)', code.replace('«', '').replace('»', '')):
        if not ALLOWED_OPTIONS.match(m.group(1)):
            problems.append(f'{rel}: set_option {m.group(1)} is not on the allowlist')
    return problems


def main() -> int:
    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else 'PercLib')
    files = sorted(root.rglob('*.lean')) + [root.with_suffix('.lean')]
    problems, n = [], 0
    for f in files:
        if not f.exists():
            continue
        n += 1
        problems += check_file(f.as_posix(), f.read_text(encoding='utf-8'))
    for p in problems:
        print('FAIL', p)
    if problems:
        print(f'Forbidden-construct scan failed: {len(problems)} problem(s) in {n} files.')
        return 1
    print(f'Forbidden-construct scan passed: {n} files under {root}.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
