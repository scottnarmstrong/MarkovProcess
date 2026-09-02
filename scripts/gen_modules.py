#!/usr/bin/env python3
"""Regenerate MODULES.md from module docstrings.

Each module contributes one line: its title (the `# ...` heading of the module docstring) and the
first sentence of the docstring body.  Run from the repository root:

    python3 scripts/gen_modules.py > MODULES.md
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / "MarkovProcess"

DOC_RE = re.compile(r"/-!(.*?)-/", re.DOTALL)


def describe(path: Path) -> str:
    text = path.read_text(encoding="utf-8")
    m = DOC_RE.search(text)
    if not m:
        return "(no module docstring)"
    body = m.group(1).strip()
    lines = [ln.strip() for ln in body.splitlines()]
    title = ""
    rest: list[str] = []
    for ln in lines:
        if not title and ln.startswith("#"):
            title = ln.lstrip("#").strip()
        elif ln.startswith("#"):
            break  # stop at the next heading
        else:
            rest.append(ln)
    para = " ".join(x for x in rest if x)
    # first sentence: up to the first period followed by a space or end
    sm = re.match(r"(.*?\.)(\s|$)", para)
    first = sm.group(1) if sm else para
    first = first.strip()
    if title and first:
        return f"{title}. {first}"
    return title or first or "(empty module docstring)"


def main() -> None:
    modules = sorted(LIB.rglob("*.lean"))
    by_dir: dict[str, list[tuple[str, str]]] = {}
    for p in modules:
        rel = p.relative_to(LIB).with_suffix("")
        parts = rel.parts
        section = parts[0] if len(parts) > 1 else parts[0]
        name = ".".join(parts)
        by_dir.setdefault(section, []).append((name, describe(p)))
    out = ["# Module index", "",
           "Generated from module docstrings (title and first sentence). One line per module.",
           "Regenerate with `python3 scripts/gen_modules.py > MODULES.md`.", ""]
    order = ["Main"] + sorted(s for s in by_dir if s != "Main")
    for section in order:
        if section not in by_dir:
            continue
        out.append(f"## {section}")
        out.append("")
        for name, desc in by_dir[section]:
            out.append(f"- `{name}`: {desc}")
        out.append("")
    sys.stdout.write("\n".join(out))


if __name__ == "__main__":
    main()
