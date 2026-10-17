#!/bin/bash
# After the (L=7,k=6,r=3) refinement converges: minimise, certify, verify independently, generate Lean, build.
set -x
cd "$(dirname "$0")"
D=../data
until grep -qE "min_mean|Traceback" $D/refine_L7_k6_r3.log; do sleep 30; done
grep -q Traceback $D/refine_L7_k6_r3.log && exit 1
python3 minimize_fast.py --L 7 --k 6 --K 5 --radius 3 > $D/minimize_L7k6.log 2>&1 || exit 1
python3 certify_direction.py --set $D/minimal_L7_k6_K5_r3.json --workers 4 --out $D/direction_certificates_k6.json > $D/certify_direction_k6.log 2>&1 || exit 1
python3 refine_fast.py --L 7 --k 6 --K 5 --radius 3 --index $D/direction_certificates_k6.json --out $D/direction_bound_L7_k6.json > $D/direction_bound_L7_k6.log 2>&1 || exit 1
python3 gen_lean_automaton_k.py --index $D/direction_certificates_k6.json --L 7 --k 6 --radius 3 > $D/gen_k6.log 2>&1 || exit 1
export PATH=$HOME/.elan/bin:$PATH
CORE=/home/user/Snake-in-the-box-in-9/work/spectral/.verification/strengthened-ubgvnend/core/.lake/build/lib/lean
B=/home/user/Snake-in-the-box-in-9/work/spectral/.verification/strengthened-ubgvnend
S=/home/user/Snake-in-the-box-in-9/work/spectral/stronger
mkdir -p /tmp/lb3 && cp $S/WindowAutomatonK6R3*.lean $S/AggregateDirectionK6R3Conditional.lean /tmp/lb3/
export LP=/tmp/lb3:$B:$CORE:$HOME/.elan/toolchains/leanprover--lean4---v4.19.0/lib/lean
bash /tmp/lb3/build.sh K6R3 > $D/build_k6.log 2>&1
python3 judge.py --index $D/direction_certificates_k6.json --workers 4 --out $D/judge_direction_k6.json > $D/judge_direction_k6.log 2>&1
echo PIPELINE_DONE
