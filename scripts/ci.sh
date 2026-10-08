#!/usr/bin/env bash
set -euo pipefail

echo "== Testing the statement-freeze guard =="
python3 -m unittest discover -s scripts/guards -p 'test_*.py'

echo "== Checking frozen staging definitions and statements =="
guard_args=(--check --strict)
# Set this to an approved Git ref to verify against a committed baseline.
if [[ -n "${STUB_LOCK_BASELINE_REF:-}" ]]; then
  guard_args+=(--baseline-ref "$STUB_LOCK_BASELINE_REF")
fi
python3 scripts/guards/stub_lock.py "${guard_args[@]}"

echo "== Building Bosonize (Core) =="
# -DwarningAsError=true ensures any 'sorry' throws a compiler error
lake build Bosonize

echo "== Building BosonizeStubs (Staging) =="
lake build BosonizeStubs

echo "CI OK"
