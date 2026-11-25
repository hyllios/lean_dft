#!/usr/bin/env bash
# Self-test of the axiom audit: plant a custom axiom, a theorem using it and a `sorry` (in a
# Mathlib-style namespace, as ForMathlib code would be); the audit MUST flag exactly these three
# and let the clean theorem pass.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH=$HOME/.elan/toolchains/$(sed 's|leanprover/lean4:|leanprover--lean4---|' lean-toolchain)/bin:$PATH
tmp=$(mktemp --suffix=.lean)
trap 'rm -f "$tmp"' EXIT
python3 - "$tmp" <<'PY'
import sys
s = open('scripts/AxiomCheck.lean').read()
bad = '''
axiom DFT.fakeAxiom : 1 = 2
theorem DFT.usesFake : 1 = 2 := DFT.fakeAxiom
theorem Matrix.usesSorry_selfTest : (2 : Nat) + 2 = 5 := by sorry
theorem DFT.clean_selfTest : (2 : Nat) + 2 = 4 := rfl
'''
open(sys.argv[1], 'w').write(s.replace("open Lean Elab Command", bad + "\nopen Lean Elab Command", 1))
PY
out=$(lake env lean "$tmp" 2>&1 || true)
n=$(echo "$out" | grep -c "uses non-standard axioms" || true)
if [ "$n" -eq 3 ] && ! echo "$out" | grep -q "clean_selfTest uses"; then
  echo "axiom audit self-test OK (flagged $n planted violations, clean theorem passed)"
else
  echo "axiom audit self-test FAILED"; echo "$out"; exit 1
fi
