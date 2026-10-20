#!/bin/bash
# Restart-safe supervisor for the k=6 work (the cloud machine reboots now and then).
# Idempotent: run it at any time; it (re)starts only what is missing and advances the
# cap-7 chain when its refinement has terminated.
R=/home/user/Snake-in-the-box-in-9; M=$R/milestones/10-window-aggregate; D=$M/data; S=$M/scripts
export PATH=$HOME/.elan/bin:$PATH
MATHLIB=/tmp/claude-0/-home-user-Snake-in-the-box-in-9/f9d17ed0-2ed6-5b33-9fe8-21ba7f2d6530/scratchpad/mathlib
log() { echo "$(date -u +%FT%TZ) $*"; }
running() { pgrep -f "$1" > /dev/null; }

# 1. fresh reproduction of the current chain (resumable build directory)
if [ ! -f $R/outputs/strengthened-direction-k6-reproduction-manifest.json ]; then
  if ! running verify_strengthened.py; then
    log "starting reproduction"
    (cd $R && nohup python3 work/spectral/verify_strengthened.py --mathlib-dir $MATHLIB \
       --build-dir work/spectral/.verification/strengthened-k6-resume \
       --core-targets Snake9 PathStructure CubeLocal SquareCounterexample SingletonSquareLemma OptimalityTarget \
       >> outputs/strengthened-direction-k6-reproduction.log 2>&1 &)
  fi
fi

# 2. cap-7 refinement (state lives in the oracle cache; result file marks termination)
if [ ! -f $D/refine_L7_k6_K7_r3.json ]; then
  if [ ! -f $D/refine_k6c7_paused ] && ! running "refine_fast.py --L 7 --k 6 --K 7"; then
    log "starting cap-7 refinement"
    (cd $M && nohup python3 scripts/refine_fast.py --L 7 --k 6 --K 7 --radius 3 --escalate 4 --hybrid --workers 4 --slack 0.3 \
       --batch 200 --query-timeout 10 --long-timeout 120 --avoid data/avoid_k6.json >> data/refine_L7_k6_K7_r3.log 2>&1 &)
  fi
else
  # 3. the chain: minimise -> certify -> rebuild from the index -> Lean -> build
  if [ ! -f $D/pipeline_k6c7.done ] && ! running pipeline_k6c7.sh; then
    log "starting cap-7 pipeline"
    (nohup bash $S/pipeline_k6c7.sh >> $D/pipeline_k6c7.log 2>&1 &)
  fi
fi

# 4. independent judge of the k=6 certificates (resumable)
if [ ! -f $D/judge_direction_k6.json ] && ! running "judge.py --index"; then
  log "starting judge"
  (cd $S && nohup nice -n 19 python3 judge.py --index ../data/direction_certificates_k6.json --workers 1 \
     --out ../data/judge_direction_k6.json >> ../data/judge_direction_k6.log 2>&1 &)
fi
# 5. empty-square-aware (omega) refinement, five centres, eight buckets (resumable from its cache)
if [ ! -f $D/refine_omega_L7_k5_K8_r3.json ] && [ ! -f $D/omega_paused ] && ! running "refine_omega.py --L 7 --k 5 --K 8"; then
  log "starting omega refinement"
  (cd $M && nohup nice -n 10 python3 scripts/refine_omega.py --L 7 --k 5 --K 8 --radius 3 --workers 1 \
     >> data/refine_omega_L7_k5_K8_r3.log 2>&1 &)
fi

# 6. DRAT certification of the cap-7 minimal set (resumable from the index)
if [ -f $D/minimal_L7_k6_K7_r3.json ] && ! grep -q "failed 0" $D/certify_direction_k6c7.log 2>/dev/null \
   && ! running "certify_direction.py"; then
  log "starting cap-7 certification"
  (cd $S && nohup python3 certify_direction.py --set ../data/minimal_L7_k6_K7_r3.json --workers 4 \
     --out ../data/direction_certificates_k6.json >> ../data/certify_direction_k6c7.log 2>&1 &)
fi

# 7. independent judge of the cap-7 certificates (resumable through the same progress file)
if [ -f $D/pipeline_c7_certified ] && [ ! -f $D/judge_direction_k6c7.json ] && [ ! -f $D/judge_paused ] && ! running "judge.py --index"; then
  log "starting cap-7 judge"
  (cd $S && nohup nice -n 5 python3 judge.py --index ../data/direction_certificates_k6.json --workers 2 \
     --out ../data/judge_direction_k6c7.json >> ../data/judge_direction_k6c7.log 2>&1 &)
fi

# 8. the 232 set (start-state accounting, two-level radius): certify into the same index
if [ -f $D/minimal_L7_k6_K7_r3_r34.json ] && ! grep -q "failed 0" $D/certify_direction_r34.log 2>/dev/null \
   && ! running "certify_direction.py"; then
  log "starting r34 certification"
  (cd $S && nohup python3 certify_direction.py --set ../data/minimal_L7_k6_K7_r3_r34.json --workers 4 \
     --out ../data/direction_certificates_k6.json >> ../data/certify_direction_r34.log 2>&1 &)
fi

# 9. the 232 chain once the set is certified
if grep -q "failed 0" $D/certify_direction_r34.log 2>/dev/null && [ ! -f $D/pipeline_r34.done ] && ! running pipeline_r34.sh; then
  log "starting 232 pipeline"
  (nohup bash $S/pipeline_r34.sh >> $D/pipeline_r34.log 2>&1 &)
fi

# 10. seven-centre windows at cap 7, lean graph (the six-centre automaton is capped at 9/2: a cycle of counts
#     4,8,4,3,5,3 is feasible in every window of at most six centres up to radius five)
if [ ! -f $D/refine_L8_k7_K7_r3.json ] && [ ! -f $D/refine_k7_paused ] && ! running "refine_fast.py --L 8 --k 7"; then
  log "starting seven-centre refinement"
  (cd $M && nohup python3 scripts/refine_fast.py --L 8 --k 7 --K 7 --lean --incremental --rc-cycles --rc-R 0.1 --radius 3 --escalate 4 --hybrid --workers 4 --slack 0.3 \
     --batch 200 --query-timeout 10 --long-timeout 120 --avoid data/avoid_k6.json >> data/refine_L8_k7_K7_r3.log 2>&1 &)
fi

log "supervisor pass done"
