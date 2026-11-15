#!/bin/bash
# Build the context-share framework and the toy chain of milestone 35 from source, into a
# scratch directory (never into work/final_lean/.lake or work/spectral/.verification), and print
# the axioms of the main theorems.
#
#   bash milestones/35-231-lean/scripts/build_toy.sh [BUILD_DIR]
#
# Reads the already built core (work/final_lean/.lake/build/lib/lean) and 233 chain
# (work/spectral/.verification/chain) .olean files; one `lean` at a time, nice -n 10.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../../.." && pwd)
B=${1:-${TMPDIR:-/tmp}/build6sc}
mkdir -p "$B"
B=$(cd "$B" && pwd)
export PATH=/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin:$PATH
export LEAN_PATH=$ROOT/work/final_lean/.lake/build/lib/lean:$ROOT/work/spectral/.verification/chain:$B
MATHLIB=${MATHLIB:-/home/user/lean-deps/mathlib4}
S=$ROOT/work/spectral/stronger
G=$ROOT/milestones/35-231-lean/lean
build() {  # source, dotted module name
  local p=$B/$(echo "$2" | tr . /)
  mkdir -p "$(dirname "$p")"
  cp "$1" "$p.lean"
  local t0=$(date +%s)
  (cd "$MATHLIB" && nice -n 10 lake env lean --root="$B" -o "$p.olean" "$p.lean") > "$p.out" 2>&1 || { cat "$p.out"; exit 1; }
  if grep -q "declaration uses 'sorry'" "$p.out"; then cat "$p.out"; exit 1; fi
  echo "$2: ok $(( $(date +%s) - t0 ))s"
}
build "$ROOT/work/final_lean/LocalWindowShareCtx.lean" LocalWindowShareCtx
for N in C70123412A236664K15 C801234032A544643K15; do
  build "$G/LocalWindowCtxCnf/$N.lean" "LocalWindowCtxCnf.$N"
  build "$G/LocalWindowCtxUnsat/$N.lean" "LocalWindowCtxUnsat.$N"
done
for M in WindowAutomaton6SCDefs WindowAutomaton6SCV2 DirectionWindowBridge6SC WindowAutomaton6SCToyData \
         DirectionWindowBridge6SCToy AggregateDirection6SCConditional AggregateDirection6SCToy; do
  build "$S/$M.lean" "$M"
done
cat > "$B/Audit6SC.lean" <<'EOF'
import AggregateDirection6SCToy
#print axioms Snake9.LocalWindow.TagsSW.soundSC
#print axioms Snake9.LocalWindow.refuted_share_from_dir
#print axioms Snake9.DirectionWindow6SC.ctxOK7_of_refuted
#print axioms Snake9.DirectionWindow6SC.ctxOK8_of_refuted
#print axioms Snake9.DirectionWindow6SC.ctx_windows6SC
#print axioms Snake9.WindowAutomaton.total_bound6SC
#print axioms Snake9.WindowAutomaton.check6SCAt_of_W
#print axioms Snake9.upper_of_refuted6SC
#print axioms Snake9.DirectionWindow6SC.ctx7_C70123412A236664K15
#print axioms Snake9.DirectionWindow6SC.ctx8_C801234032A544643K15
#print axioms Snake9.DirectionWindow6SC.label6SCToy
#print axioms Snake9.upper_254_toy6SC
EOF
(cd "$MATHLIB" && lake env lean --root="$B" "$B/Audit6SC.lean") | tee "$B/Audit6SC.out"
if grep "depends on axioms" "$B/Audit6SC.out" | grep -vq "\[propext, Classical.choice, Quot.sound\]\|\[propext, Quot.sound\]\|\[propext\]"; then
  echo "AXIOM AUDIT FAILED"; exit 1
fi
echo "AXIOM AUDIT PASSED"
