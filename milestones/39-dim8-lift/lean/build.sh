#!/bin/bash
# Build the facet-split reduction with core Lean 4.35 (no mathlib, no lake).
set -e
cd "$(dirname "$0")"
L=${LEAN:-/opt/lean-4.35.0-linux/bin/lean}
mkdir -p build
for m in Snake9Core Sums Bits Premise Lift1 Lift2 Lift3 Lift4 Lift5 Dim8Lift; do
  echo "== $m"; LEAN_PATH=build $L -o build/$m.olean $m.lean 2>&1 | grep -E "error|axioms" || true
done
