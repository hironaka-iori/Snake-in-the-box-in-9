#!/bin/bash
# The 232 chain once every window of the start-accounting set is certified:
# index check (start-aware) -> Lean generation from the index -> reproduction with both cap-7 chains.
set -e
R=/home/user/Snake-in-the-box-in-9; M=$R/milestones/10-window-aggregate; D=$M/data; S=$M/scripts
export PATH=/root/.elan/toolchains/leanprover--lean4---v4.19.0/bin:$HOME/.elan/bin:$PATH
MATHLIB=/tmp/claude-0/-home-user-Snake-in-the-box-in-9/f9d17ed0-2ed6-5b33-9fe8-21ba7f2d6530/scratchpad/mathlib
log() { echo "$(date -u +%FT%TZ) $*"; }
grep -q "failed 0" $D/certify_direction_r34.log || { log "certification not finished"; exit 1; }
cd $S
if [ ! -f $D/direction_bound_L7_k6_K7_r34.json ]; then
  log "index check"
  python3 refine_fast.py --L 7 --k 6 --K 7 --index ../data/direction_certificates_k6.json --start \
    --out ../data/direction_bound_L7_k6_K7_r34.json
fi
if [ ! -f $D/pipeline_r34.generated ]; then
  log "Lean generation"
  python3 gen_lean_swar.py --index ../data/direction_certificates_k6.json --set ../data/minimal_L7_k6_K7_r3_r34.json \
    --L 7 --k 6 --K 7 --lam 9/2 --start
  touch $D/pipeline_r34.generated
fi
log "reproduction"
cd $R
python3 work/spectral/verify_strengthened.py --mathlib-dir $MATHLIB \
  --build-dir work/spectral/.verification/strengthened-k6-resume \
  --core-targets Snake9 PathStructure CubeLocal SquareCounterexample SingletonSquareLemma OptimalityTarget \
  --extra-chains K6R3C7W K6R34C7W --jobs 4
cp work/spectral/.verification/strengthened-k6-resume/manifest.json outputs/strengthened-direction-232-reproduction-manifest.json
touch $D/pipeline_r34.done
log "done"
