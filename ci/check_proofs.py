#!/usr/bin/env python3
"""CI checks for the Lean formalization.

1. No proof shortcuts in production Lean files (comments and strings are ignored).
2. Every Lean module of Section3/ and Section4/ is a root of its Lake library.
3. Every theorem in ci/expected_theorems.txt has an axiom report in the checker logs,
   and every report lists only propext, Classical.choice and Quot.sound.

Usage: python3 ci/check_proofs.py LOG [LOG ...]
"""
import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = [
    (r"\bsorry\b", "sorry"),
    (r"\badmit\b", "admit"),
    (r"\bnative_decide\b", "native_decide"),
    (r"\bunsafe\b", "unsafe"),
    (r"(?m)^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:private\s+|protected\s+)?axiom\b", "axiom declaration"),
    (r"\bimplemented_by\b", "implemented_by"),
    (r"@\[\s*extern\b", "extern"),
    (r"\bdebug\.skipKernelTC\b", "debug.skipKernelTC"),
]
DIRS = ["Section3", "Section4"]


def strip_comments(src: str) -> str:
    """Remove Lean comments (nested block comments, line comments) and string literals."""
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith('"', i):
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""')
            i = j + 1
        elif src.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
        else:
            if depth == 0 or src[i] == "\n":
                out.append(src[i])
            i += 1
    return "".join(out)


def main() -> int:
    errors = []
    files = [p for d in DIRS for p in sorted((ROOT / d).glob("*.lean"))]
    for path in files:
        code = strip_comments(path.read_text())
        for pat, name in FORBIDDEN:
            for m in re.finditer(pat, code):
                line = code.count("\n", 0, m.start()) + 1
                errors.append(f"{path.relative_to(ROOT)}:{line}: forbidden {name}")
    print(f"shortcut scan: {len(files)} files")

    lake = tomllib.loads((ROOT / "lakefile.toml").read_text())
    for lib in lake.get("lean_lib", []):
        src = lib.get("srcDir")
        if src not in ("Section3", "Section4"):
            continue
        roots = set(lib.get("roots", []))
        for path in sorted((ROOT / src).glob("*.lean")):
            if path.stem not in roots and path.stem != "Check":
                errors.append(f"{path.relative_to(ROOT)}: not a root of library {lib['name']}")
        print(f"library {lib['name']}: {len(roots)} roots")

    expected = [l.strip() for l in (ROOT / "ci/expected_theorems.txt").read_text().splitlines()
                if l.strip() and not l.startswith("#")]
    reports = {}
    for log in sys.argv[1:]:
        text = Path(log).read_text()
        if re.search(r"(?m)^\S+:\d+:\d+: error", text) or "error:" in text:
            errors.append(f"{log}: checker reported an error")
        for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
            reports[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
        for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
            reports[m.group(1)] = set()
    for name, axioms in sorted(reports.items()):
        bad = axioms - ALLOWED
        if bad:
            errors.append(f"{name}: unexpected axioms {sorted(bad)}")
    for name in expected:
        full = name if name in reports else f"GradientKey.Concrete.{name}"
        if full not in reports:
            errors.append(f"{name}: no axiom report in the checker output")
    print(f"axiom reports: {len(reports)}, expected theorems: {len(expected)}")

    for e in errors:
        print("ERROR", e)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
