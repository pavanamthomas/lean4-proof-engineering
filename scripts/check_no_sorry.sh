#!/usr/bin/env bash
# Reject forbidden proof holes and custom axiom declarations in project sources.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

mapfile -t lean_files < <(find . -name '*.lean' -not -path './.lake/*' | sort)

if [[ ${#lean_files[@]} -eq 0 ]]; then
  echo "check_no_sorry: no project .lean files found" >&2
  exit 1
fi

fail=0

if grep -nE '(^|[^A-Za-z0-9_])(sorry|admit)([^A-Za-z0-9_]|$)' "${lean_files[@]}"; then
  echo "check_no_sorry: found sorry or admit in project Lean sources" >&2
  fail=1
else
  echo "check_no_sorry: no sorry or admit tokens in project Lean sources"
fi

if grep -nE '^[[:space:]]*axiom[[:space:]]' "${lean_files[@]}"; then
  echo "check_no_sorry: found a custom axiom declaration in project Lean sources" >&2
  fail=1
else
  echo "check_no_sorry: no custom axiom declarations in project Lean sources"
fi

exit "${fail}"
