#!/usr/bin/env python3
"""Conservative D-24 proof-only classification of a change, run locally by LEAD."""
import argparse
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = set('def abbrev opaque axiom axioms constant constants inductive coinductive structure '
                'class instance notation syntax macro macro_rules elab elab_rules initialize '
                'builtin_initialize register_option register_builtin_option attribute export '
                'run_cmd run_elab run_tac deriving tag'.split())


def _is_letter_like(c):
    """Lean's `isLetterLike`: Greek (without λ, Π, Σ), Coptic, Greek extended,
    letterlike symbols and mathematical script letters."""
    n = ord(c)
    return ((0x3b1 <= n <= 0x3c9 and n != 0x3bb) or (0x391 <= n <= 0x3a9 and n not in (0x3a0, 0x3a3))
            or 0x3ca <= n <= 0x3fb or 0x1f00 <= n <= 0x1ffe or 0x2100 <= n <= 0x214f
            or 0x1d49c <= n <= 0x1d59f)


def _is_id_first(c):
    return c.isascii() and c.isalpha() or c == '_' or _is_letter_like(c)


def _is_id_rest(c):
    """Lean's `isIdRest`: ASCII alphanumerics, `_ ' ! ?`, letterlike and subscripts."""
    n = ord(c)
    return (c.isascii() and c.isalnum() or c in "_'!?" or _is_letter_like(c)
            or 0x2080 <= n <= 0x209c or 0x1d62 <= n <= 0x1d6a or n == 0x2c7c)


# The escapes Lean accepts after `\` in string and character literals (checked on v4.35.0);
# on any other escape Lean abandons the literal and lexes the rest as code.
ESCAPE = re.compile(r"""\\(?:[\\"'ntr]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4})""")
CHAR_LITERAL = re.compile("'(?:" + ESCAPE.pattern + r"|[^\\])'", re.S)


def code_without_literals(text):
    """Erase nested comments, string and character literals before the conservative
    token check, keeping identifiers (including `«…»` ones) verbatim.

    The scan follows Lean's lexer where a mismatch could hide code: inside `«…»` (copied
    through to the next `»`) `--`, `/-` and `"` open nothing; `'` starts a character
    literal unless it continues an identifier (`h'`). A string literal containing `{` is
    refused, since only its context (`s!`, `m!`, `throwError`, …) tells whether it is
    interpolated, i.e. contains code. An escape outside `ESCAPE` (in a string, also
    `\\` + newline) is refused, since Lean then abandons the literal and lexes on as code."""
    result, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if text.startswith('/-', i):
            depth = 1
            i += 2
            result.append(' ')
            continue
        if text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
            continue
        raw = re.match(r'r(#+)?"', text[i:])
        if raw:
            closing = '"' + (raw[1] or '')
            end = text.find(closing, i + len(raw[0]))
            if end < 0:
                raise ValueError('Unterminated raw string')
            i = end + len(closing)
            result.append(' ')
            continue
        if text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                if text[i] == '{':
                    raise ValueError('String literal containing `{` (possibly interpolated)')
                if text[i] == '\\':
                    if text.startswith('\n', i + 1):
                        i += 2
                        continue
                    esc = ESCAPE.match(text, i)
                    if not esc:
                        raise ValueError('invalid escape in string literal')
                    i = esc.end()
                    continue
                i += 1
            if i >= len(text):
                raise ValueError('Unterminated string')
            i += 1
            result.append(' ')
            continue
        if text[i] == '«' or _is_id_first(text[i]):
            # An identifier: atoms of letters or `«…»`, joined by `.`.
            start = i
            while True:
                if text[i] == '«':
                    end = text.find('»', i + 1)
                    if end < 0:
                        raise ValueError('Unterminated «')
                    i = end + 1
                else:
                    i += 1
                    while i < len(text) and _is_id_rest(text[i]):
                        i += 1
                if (i + 1 < len(text) and text[i] == '.'
                        and (text[i + 1] == '«' or _is_id_first(text[i + 1]))):
                    i += 1
                    continue
                break
            result.append(text[start:i])
            continue
        if text[i].isascii() and text[i].isdigit():
            # A numeral, so that a following `'` starts a character literal, as in Lean.
            start = i
            while i < len(text) and text[i].isascii() and (text[i].isalnum() or text[i] == '_'):
                i += 1
            result.append(text[start:i])
            continue
        if text[i] == "'":
            m = CHAR_LITERAL.match(text, i)
            if m:
                i = m.end()
                result.append(' ')
                continue
            if text.startswith('\\', i + 1):
                raise ValueError('invalid escape in character literal')
        result.append(text[i])
        i += 1
    if depth:
        raise ValueError('Unterminated comment')
    return ''.join(result)


def check_paths_and_source(changes):
    for path, source in changes.items():
        p = Path(path)
        if p.suffix != '.lean' or p.name in ('Basic.lean', 'Defs.lean'):
            raise ValueError(f'Proof PR touches an interface/non-Lean file: {path}')
        code = code_without_literals(source or '')
        if path == 'PercLib.lean':
            if any(line.strip() and not re.fullmatch(
                    r'(?:module|(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?[\w.]+)',
                    line.strip()) for line in code.splitlines()):
                raise ValueError('The root may change imports only in a proof PR')
        bad = FORBIDDEN.intersection(re.findall(r'[A-Za-z_][A-Za-z0-9_]*', code))
        if bad:
            raise ValueError(f'Interface/metaprogramming tokens in {path}: {sorted(bad)}')


def compiled_interfaces(raw):
    return {d['name']: {k: d[k] for k in
            ('kind', 'module', 'public', 'universes', 'type', 'value', 'related')}
            for d in raw['declarations'] if d['kind'] != 'theorem'}


def tagged_statements(raw):
    return {d['name']: {k: d[k] for k in ('tag', 'type', 'statement_expr')}
            for d in raw['declarations'] if d['tag'] is not None}


def check_compiled(base, head):
    before, after = compiled_interfaces(base), compiled_interfaces(head)
    changed = [n for n in sorted(before.keys() | after.keys()) if before.get(n) != after.get(n)]
    if changed:
        raise ValueError('Compiled non-theorem declarations changed: ' + ', '.join(changed))
    if tagged_statements(base) != tagged_statements(head):
        raise ValueError('Tagged statements/associations changed; interface review required')


def command(*args, cwd=ROOT, capture=False):
    if capture:
        return subprocess.check_output(args, cwd=cwd, text=True)
    subprocess.run(args, cwd=cwd, check=True)


def main():
    """Classify the change from BASE to the working tree as proof-only or interface.

    Exit 0: proof-only (passes on the gate alone). Exit 3: interface change, which needs
    a fresh auditor's approval (D-34); the reason is printed. Other exits are errors.
    The compiled comparison needs the extracted manifest of BASE (`--base-raw`), which
    the gate saves for every gated commit, and of the head (`--head-raw`).
    """
    parser = argparse.ArgumentParser(description=main.__doc__)
    parser.add_argument('--base', required=True, help='base commit (the integration tip)')
    parser.add_argument('--base-raw', type=Path, help='ExtractManifest output for BASE')
    parser.add_argument('--head-raw', type=Path, default=Path('.lake/manifest-raw.json'))
    args = parser.parse_args()
    base = command('git', 'rev-parse', '--verify', args.base + '^{commit}', capture=True).strip()
    paths = command('git', 'diff', '--name-only', '--no-renames', base, capture=True).splitlines()
    paths += command('git', 'ls-files', '--others', '--exclude-standard', capture=True).splitlines()
    lean = [p for p in paths if p.endswith('.lean') and not p.startswith('scripts/')]
    changes = {p: (ROOT / p).read_text() if (ROOT / p).exists() else None for p in lean}
    try:
        check_paths_and_source(changes)
        if args.base_raw is None:
            raise ValueError('no compiled manifest of the base given; cannot confirm proof-only')
        check_compiled(json.loads(args.base_raw.read_text()), json.loads(args.head_raw.read_text()))
    except ValueError as e:
        print(f'INTERFACE change against {base[:12]}: {e}')
        raise SystemExit(3)
    print(f'PROOF-ONLY change against {base[:12]}: {len(lean)} Lean file(s), '
          'no compiled interface change.')


if __name__ == '__main__':
    main()
