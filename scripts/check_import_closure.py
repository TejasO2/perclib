#!/usr/bin/env python3
"""Fail if a Lean file of the library is not imported, directly or transitively,
by the library root.

Usage: python3 scripts/check_import_closure.py [ROOT]      (default ROOT: PercLib)

The default build and the rooted axiom audit only see modules reachable from
ROOT.lean. A file under ROOT/ that is not reachable is never compiled, so it
could contain anything. This check reads import headers only and needs no Lean
toolchain. It uses the Python standard library only.
"""
from __future__ import annotations

import pathlib
import re
import sys


def strip_comments(text: str) -> str:
    """Remove `--` line comments and nested `/- -/` block comments."""
    out = []
    i, depth, n = 0, 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth:
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif two == "--":
            while i < n and text[i] != "\n":
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


IMPORT = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)\s*$")


def imports_of(path: pathlib.Path) -> list[str]:
    """Module names imported by the header of `path`.

    Imports come first in a Lean file, after an optional `module` keyword, so
    reading stops at the first line that is neither.
    """
    found = []
    for raw in strip_comments(path.read_text(encoding="utf-8")).splitlines():
        line = raw.strip()
        if not line or line == "module" or line == "prelude":
            continue
        match = IMPORT.match(line)
        if not match:
            break
        found.append(match.group(1))
    return found


def main() -> int:
    root = sys.argv[1] if len(sys.argv) > 1 else "PercLib"
    repo = pathlib.Path(__file__).resolve().parent.parent
    root_file = repo / f"{root}.lean"
    if not root_file.is_file():
        print(f"error: {root}.lean not found in {repo}", file=sys.stderr)
        return 2

    def file_of(module: str) -> pathlib.Path:
        return repo / (module.replace(".", "/") + ".lean")

    reached, todo, missing = set(), [root], []
    while todo:
        module = todo.pop()
        if module in reached:
            continue
        reached.add(module)
        for imported in imports_of(file_of(module)):
            if imported != root and not imported.startswith(root + "."):
                continue  # a dependency such as Mathlib
            if not file_of(imported).is_file():
                missing.append((module, imported))
                continue
            todo.append(imported)

    on_disk = {root} | {
        ".".join(p.relative_to(repo).with_suffix("").parts)
        for p in (repo / root).rglob("*.lean")
    }
    unimported = sorted(on_disk - reached)

    for module, imported in missing:
        print(f"error: {module} imports {imported}, which has no source file")
    for module in unimported:
        print(f"error: {module.replace('.', '/')}.lean is not in the import closure of {root}.lean")
    if missing or unimported:
        print(f"\nAdd each new module to {root}.lean, or to a module that {root}.lean imports.")
        return 1
    print(f"ok: all {len(on_disk)} modules of {root} are in the import closure of {root}.lean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
