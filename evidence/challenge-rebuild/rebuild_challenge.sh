#!/bin/bash
set -x
set -o pipefail
export XDG_CACHE_HOME="$HOME/rh-audit/cache"
export MATHLIB_CACHE_DIR="$HOME/rh-audit/cache/mathlib"
export PATH="$HOME/rh-audit/tools/lean-4.33.1-darwin_aarch64/bin:$PATH"
cd "$HOME/rh-audit/challenge-rebuild"
date
ok=0
for attempt in 1 2 3 4 5 6; do
  rm -rf .lake/packages/batteries.tmp
  if lake exe cache get 2>&1 | tail -12; then ok=1; break; fi
  echo "cache get attempt $attempt failed; retrying"; sleep 10
done
[ $ok = 1 ] || { echo "CACHE GET FAILED"; exit 13; }
date
# refuse to compile Mathlib from source: --no-build style guard via olean presence
ls .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean || { echo "NO MATHLIB OLEAN"; exit 14; }
lake build Challenge 2>&1 | tail -8 || exit 15
date
cd "$HOME/rh-audit/tools"
if [ ! -d lean4export ]; then git clone -q https://github.com/leanprover/lean4export.git || exit 16; fi
cd lean4export && git checkout -q v4.33.0 && git log -1 --format='%H %ad %s' && (lake build 2>&1 | tail -5) || exit 17
ls .lake/build/bin
cd "$HOME/rh-audit/challenge-rebuild"
lake env "$HOME/rh-audit/tools/lean4export/.lake/build/bin/lean4export" Challenge -- $(cat export-targets.txt | tr '\n' ' ') > my_challenge.ndjson || exit 18
ls -la my_challenge.ndjson
shasum -a 256 my_challenge.ndjson
echo "published: bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9"
date
echo DONE
