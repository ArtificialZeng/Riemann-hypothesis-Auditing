#!/bin/zsh
# usage: leanc.sh /absolute/path/File.lean   -- elaborates one file with Lean 4.33.1 against the official Mathlib build; writes nothing
P=$HOME/rh-audit/challenge-rebuild/.lake/packages
export LEAN_PATH="$P/Cli/.lake/build/lib/lean:$P/batteries/.lake/build/lib/lean:$P/Qq/.lake/build/lib/lean:$P/aesop/.lake/build/lib/lean:$P/proofwidgets/.lake/build/lib/lean:$P/importGraph/.lake/build/lib/lean:$P/LeanSearchClient/.lake/build/lib/lean:$P/plausible/.lake/build/lib/lean:$P/mathlib/.lake/build/lib/lean"
exec $HOME/rh-audit/tools/lean-4.33.1-darwin_aarch64/bin/lean "$@"
