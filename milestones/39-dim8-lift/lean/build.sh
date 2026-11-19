#!/bin/bash
# Build the milestone-39 Lean files with core Lean 4.35 (no mathlib, no lake).
# LocalWindowModel and LratV3 are taken from work/final_lean (LratV3 with the one 4.35 fix of
# lean435/tools/port.py); in the audited stack they are the ported modules of the same names.
set -e
cd "$(dirname "$0")"
L=${LEAN:-/opt/lean-4.35.0-linux/bin/lean}
mkdir -p build gen
cp ../../../work/final_lean/LocalWindowModel.lean gen/
sed 's/rw \[Option.mem_toList, Option.mem_def, Option.some.injEq\] at hy/simp only [Option.mem_toList, Option.mem_def, Option.some.injEq] at hy/' \
  ../../../work/final_lean/LratV3.lean > gen/LratV3.lean
for m in gen/LocalWindowModel gen/LratV3 Snake9Core Sums Bits Premise Lift1 Lift2 Lift3 Lift4 Lift5 Dim8Lift Counter CubeCnf CubeBridge1 CubeBridge2 CubeBridge3 CubeBridge4 CubeBridge5 Sym SymPit Glue1 Moves Glue2 ${EXTRA:-}; do
  b=$(basename $m); echo "== $b"; LEAN_PATH=build $L -o build/$b.olean $m.lean 2>&1 | grep -E "error|axioms" || true
done
