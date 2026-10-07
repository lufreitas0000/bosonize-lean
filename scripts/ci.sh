#!/usr/bin/env bash
set -euo pipefail

echo "== Building Bosonize (Core) =="
# -DwarningAsError=true ensures any 'sorry' throws a compiler error
lake build Bosonize

echo "== Building BosonizeStubs (Staging) =="
lake build BosonizeStubs

echo "CI OK"
