#!/usr/bin/env bash
# Release gate: the tracked tree must be public-facing.
# Run from the repository root; exits non-zero on the first class of violation found.
set -uo pipefail
cd "$(dirname "$0")/.."
status=0

echo "== tracked files: no local paths, scratch references, or development-process vocabulary =="
if git grep -n -I -i -E \
    '/root/|scratchpad|Algsuperdiff|DivergenceFormProcess|Superdiffusion|Theorem A\b|source-facing|orchestrat|claude\.ai|session_0|\bpacket\b|\bcampaign\b|wish-list|handoff' \
    -- . ':!scripts/release_check.sh'; then
  echo "::error::development-process vocabulary or local paths found in tracked files"
  status=1
fi

echo "== no sorry, axiom, or heartbeat override in the library =="
if git grep -n -E '\bsorry\b|^[[:space:]]*axiom[[:space:]]|maxHeartbeats' -- 'MarkovProcess/*.lean' 'MarkovProcess.lean' 'docs/*.lean'; then
  echo "::error::sorry, axiom, or heartbeat override found"
  status=1
fi

echo "== every comparator challenge has exactly one sorry, the solutions none =="
for c in Audit/*/Challenge.lean; do
  n_challenge=$(grep -c '\bsorry\b' "$c" || true)
  if [ "$n_challenge" -ne 1 ]; then
    echo "::error file=$c::challenge has $n_challenge sorry (expected 1)"
    status=1
  fi
done
n_solution=$(git grep -c '\bsorry\b' -- 'Audit/*/Solution.lean' 'Audit/*/SolutionBasic.lean' | awk -F: '{s+=$2} END {print s+0}')
if [ "$n_solution" -ne 0 ]; then
  echo "::error::solutions have $n_solution sorry (expected 0)"
  status=1
fi

echo "== no Lean file over 1500 lines =="
while IFS= read -r f; do
  n=$(wc -l < "$f")
  if [ "$n" -gt 1500 ]; then
    echo "::error file=$f::$f has $n lines"
    status=1
  fi
done < <(git ls-files '*.lean')

echo "== no untracked or ignored stray files besides .lake =="
if git status --porcelain --ignored | grep -v '^!! \.lake/$' | grep -q .; then
  git status --porcelain --ignored | grep -v '^!! \.lake/$'
  echo "::error::stray files in the working tree"
  status=1
fi

echo "== README Lean excerpts are verbatim from the source =="
if ! python3 scripts/check_readme.py; then
  status=1
fi

echo "== module index is current =="
if ! diff -q <(python3 scripts/gen_modules.py) MODULES.md >/dev/null; then
  echo "::error::MODULES.md is stale; run: python3 scripts/gen_modules.py > MODULES.md"
  status=1
fi

if [ "$status" -eq 0 ]; then echo "release check passed"; fi
exit "$status"
