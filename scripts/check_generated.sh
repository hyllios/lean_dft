#!/usr/bin/env bash
# Generated Lean files must be reproducible: regenerate each one in a scratch tree and compare byte for byte.
# Needs python3 with sympy (CI installs it). Usage: scripts/check_generated.sh [python]
set -euo pipefail
cd "$(dirname "$0")/.."
PY="${1:-python3}"
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
status=0
# generator script -> generated file (path relative to the repository root)
for pair in "gen_hubbard_sym_lean.py:DFT/Lattice/Spin/HubbardCertificates.lean"; do
  gen=${pair%%:*}; out=${pair#*:}
  mkdir -p "$tmp/scripts" "$tmp/$(dirname "$out")"
  cp "scripts/$gen" "$tmp/scripts/"
  (cd "$tmp/scripts" && "$PY" "$gen" > /dev/null)
  if cmp -s "$out" "$tmp/$out"; then echo "reproducible: $out (scripts/$gen)"
  else echo "NOT reproducible: $out differs from the output of scripts/$gen"; diff "$out" "$tmp/$out" | head -20; status=1; fi
done
exit $status
