#!/usr/bin/env bash
# Compile the consumer guide's code blocks against the built library.
# Run from the repository root after `lake build`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean docs/ConsumerGuide.lean
echo "consumer guide probe compiled"
