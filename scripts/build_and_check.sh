#!/usr/bin/env bash
# Full local verification: hole check, mathlib cache, lake build.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

echo "==> toolchain"
cat lean-toolchain
echo

echo "==> hole and axiom check"
bash scripts/check_no_sorry.sh
echo

if [[ ! -d .lake/packages/mathlib ]]; then
  echo "==> lake update (mathlib not present)"
  lake update
fi

echo "==> mathlib cache"
lake exe cache get
echo

echo "==> lake build"
lake build
echo

echo "build_and_check: completed"
