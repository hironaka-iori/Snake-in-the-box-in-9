#!/bin/bash
# Cap-7 six-centre chain, each stage skipped when its output exists (restart-safe).
cd "$(dirname "$0")"; D=../data; R=../../..; export PATH=$HOME/.elan/bin:$PATH
set -e
[ -f $D/minimal_L7_k6_K7_r3.json ] || python3 minimize_fast.py --L 7 --k 6 --K 7 --radius 3 --avoid $D/avoid_k6.json > $D/minimize_L7k6_K7.log 2>&1
python3 certify_direction.py --set $D/minimal_L7_k6_K7_r3.json --workers 2 --out $D/direction_certificates_k6.json > $D/certify_direction_k6c7.log 2>&1
grep -q "failed 0" $D/certify_direction_k6c7.log
python3 refine_fast.py --L 7 --k 6 --K 7 --radius 3 --index $D/direction_certificates_k6.json --out $D/direction_bound_L7_k6_K7.json > $D/direction_bound_L7_k6_K7.log 2>&1
python3 gen_lean_automaton_k.py --index $D/direction_certificates_k6.json --set $D/minimal_L7_k6_K7_r3.json --L 7 --k 6 --K 7 --radius 3 > $D/gen_lean_K6R3C7.log 2>&1
# scratch build of the generated chain (the official reproduction follows separately)
B=$R/work/spectral/.verification/strengthened-ubgvnend; W=/tmp/lb_c7; mkdir -p $W
cp $R/work/spectral/stronger/WindowAutomatonK6R3C7*.lean $R/work/spectral/stronger/AggregateDirectionK6R3C7Conditional.lean $R/work/spectral/stronger/WindowAutomatonLoop.lean $R/work/spectral/stronger/WindowAutomatonSym.lean $W/
export LP=$W:$B:$B/core/.lake/build/lib/lean:$HOME/.elan/toolchains/leanprover--lean4---v4.19.0/lib/lean
cd $W
for m in WindowAutomatonLoop WindowAutomatonSym WindowAutomatonK6R3C7Data; do
  [ -f $m.olean ] && [ $m.olean -nt $m.lean ] || LEAN_PATH=$LP lean -o $m.olean $m.lean
done
ls WindowAutomatonK6R3C7Shard*.lean | sed 's/.lean//' | xargs -P 3 -I{} sh -c '[ -f {}.olean ] && [ {}.olean -nt {}.lean ] || (start=$(date +%s); env LEAN_PATH=$LP lean -o {}.olean {}.lean 2>&1 | grep -v "^warning\|^note"; echo "{} $(( $(date +%s) - start )) s")'
for m in WindowAutomatonK6R3C7Table WindowAutomatonK6R3C7Sequence; do
  [ -f $m.olean ] && [ $m.olean -nt $m.lean ] || LEAN_PATH=$LP lean -o $m.olean $m.lean 2>&1 | grep -v "^warning\|^note"
done
cd /tmp/claude-0/-home-user-Snake-in-the-box-in-9/f9d17ed0-2ed6-5b33-9fe8-21ba7f2d6530/scratchpad/mathlib
LEAN_PATH=$LP lake env lean --root=$W -o $W/AggregateDirectionK6R3C7Conditional.olean $W/AggregateDirectionK6R3C7Conditional.lean > $W/wrapper.log 2>&1
grep -v "^warning\|^note" $W/wrapper.log
grep -q "_of_direction_windowsK6R3C7' depends on axioms: \[propext, Classical.choice, Quot.sound\]" $W/wrapper.log && touch $D/pipeline_k6c7.done
echo PIPELINE_C7_DONE
