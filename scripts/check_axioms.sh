#!/usr/bin/env bash
# Axiom audit: every declaration defined in a DFT/QM/ForMathlib module may use only
# propext, Classical.choice and Quot.sound (a `sorry` shows up as `sorryAx` and fails).
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH=$HOME/.elan/toolchains/$(sed 's|leanprover/lean4:|leanprover--lean4---|' lean-toolchain)/bin:$PATH
lake build ForMathlib QM DFT >/dev/null
out=$(lake env lean scripts/AxiomCheck.lean 2>&1) || { echo "$out"; exit 1; }
echo "$out"
echo "$out" | grep -q "axiom check OK" || exit 1
