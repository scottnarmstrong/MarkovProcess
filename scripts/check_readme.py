#!/usr/bin/env python3
"""Check that the Lean excerpts in README.md and docs/CONSUMER_GUIDE.md are verbatim from the source,
and that the module and line counts stated in README.md are current.

README: between the markers `<!-- BEGIN verbatim -->` and `<!-- END verbatim -->`, every fenced
```lean block must be preceded by an HTML comment `<!-- source: <path> -->` naming the Lean file
it is taken from.  The block, split at lines consisting only of `...`, must occur verbatim (as
contiguous text, trailing whitespace ignored) in that file.

Guide: every fenced ```lean block of docs/CONSUMER_GUIDE.md must occur verbatim in
docs/ConsumerGuide.lean, the file compiled by scripts/check_docs.sh.

Counts: the README sentence "N Lean modules plus the root module ..., about L lines" must give the
number of tracked `MarkovProcess/**/*.lean` files exactly and their total line count to within
five percent.  Exits non-zero and prints every offence otherwise.
"""
import subprocess
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
README = ROOT / "README.md"


def normalize(text: str) -> str:
    return "\n".join(line.rstrip() for line in text.splitlines())


def main() -> int:
    lines = README.read_text(encoding="utf-8").splitlines()
    status = 0
    checked = 0
    inside = False
    source = None
    block = None
    for lineno, line in enumerate(lines, start=1):
        stripped = line.strip()
        if stripped == "<!-- BEGIN verbatim -->":
            inside = True
            continue
        if stripped == "<!-- END verbatim -->":
            inside = False
            source = None
            continue
        if not inside:
            continue
        m = re.fullmatch(r"<!-- source: (\S+) -->", stripped)
        if m:
            source = m.group(1)
            continue
        if stripped == "```lean":
            block = []
            block_start = lineno
            continue
        if stripped == "```" and block is not None:
            if source is None:
                print(f"README.md:{block_start}: lean block without a <!-- source: --> comment")
                status = 1
            else:
                text = normalize((ROOT / source).read_text(encoding="utf-8"))
                for segment in re.split(r"^\.\.\.$", "\n".join(block), flags=re.M):
                    segment = normalize(segment).strip("\n")
                    if not segment:
                        continue
                    if segment not in text:
                        print(f"README.md:{block_start}: excerpt not found verbatim in {source}:")
                        print(segment)
                        status = 1
                    checked += 1
            block = None
            continue
        if block is not None:
            block.append(line)
    if checked == 0:
        print("README.md: no verbatim excerpts found between the markers")
        status = 1
    if status == 0:
        print(f"README excerpts verified: {checked} segments verbatim from the source")
    status |= check_guide()
    status |= check_counts()
    return status


def check_guide() -> int:
    guide = (ROOT / "docs" / "CONSUMER_GUIDE.md").read_text(encoding="utf-8").splitlines()
    compiled = normalize((ROOT / "docs" / "ConsumerGuide.lean").read_text(encoding="utf-8"))
    status = 0
    blocks = 0
    block = None
    for lineno, line in enumerate(guide, start=1):
        if line.strip() == "```lean":
            block = []
            block_start = lineno
        elif line.strip() == "```" and block is not None:
            text = normalize("\n".join(block)).strip("\n")
            if text and text not in compiled:
                print(f"docs/CONSUMER_GUIDE.md:{block_start}: block not verbatim in docs/ConsumerGuide.lean")
                status = 1
            blocks += 1
            block = None
        elif block is not None:
            block.append(line)
    if status == 0:
        print(f"guide blocks verified: {blocks} blocks verbatim in docs/ConsumerGuide.lean")
    return status


def check_counts() -> int:
    readme = README.read_text(encoding="utf-8")
    m = re.search(r"\*\*(\d+) Lean modules plus the root module `MarkovProcess\.lean`, about ([\d,]+) lines\*\*", readme)
    if m is None:
        print("README.md: module and line count sentence not found")
        return 1
    files = subprocess.run(["git", "ls-files", "MarkovProcess/*.lean"], cwd=ROOT, capture_output=True,
                           text=True, check=True).stdout.split()
    modules = len(files)
    lines = sum(len((ROOT / f).read_text(encoding="utf-8").splitlines()) for f in files)
    claimed_modules = int(m.group(1))
    claimed_lines = int(m.group(2).replace(",", ""))
    status = 0
    if claimed_modules != modules:
        print(f"README.md: claims {claimed_modules} modules, the tree has {modules}")
        status = 1
    if abs(claimed_lines - lines) > 0.05 * lines:
        print(f"README.md: claims about {claimed_lines} lines, the tree has {lines}")
        status = 1
    if status == 0:
        print(f"README counts verified: {modules} modules, {lines} lines")
    return status


if __name__ == "__main__":
    sys.exit(main())
