#!/bin/bash
# The 231 chain once every window of the seven-centre start-accounting set (cap 7, mean 89/19) is certified:
# index check (lean graph, start-aware, at 89/19) -> Lean generation from the index (split 16-bit SWAR chain
# K7R34C7W16) and its share-bonus 230 wrapper -> reproduction with both cap-7 six-centre chains, the new
# chain, the share-bonus 231 and the 230.
# Memory: the index check and the generator hold the 563M-edge graph (~5 GB peak); Lean modules up to ~2.7 GB each.
set -e
R=/home/user/Snake-in-the-box-in-9; M=$R/milestones/10-window-aggregate; D=$M/data; S=$M/scripts
export PATH=/root/.elan/toolchains/leanprover--lean4---v4.19.0/bin:$HOME/.elan/bin:$PATH
MATHLIB=/tmp/claude-0/-home-user-Snake-in-the-box-in-9/f9d17ed0-2ed6-5b33-9fe8-21ba7f2d6530/scratchpad/mathlib
log() { echo "$(date -u +%FT%TZ) $*"; }
grep -q "failed 0" $D/certify_direction_231.log || { log "certification not finished"; exit 1; }
cd $S
if [ ! -f $D/direction_bound_L8_k7_K7_89_19.json ]; then
  log "index check"
  # every window of the set must be drat-trim verified in the index; the automaton is rebuilt from those only
  nice -n 10 python3 lean_index.py --L 8 --k 7 --K 7 --index ../data/direction_certificates_k6.json \
    --set ../data/minimal_L8_k7_K7_r3_89_19.json --require-set --lam 89/19 \
    --out ../data/direction_bound_L8_k7_K7_89_19.json.tmp
  python3 - <<'EOF'
import json
d = json.load(open('../data/direction_bound_L8_k7_K7_89_19.json.tmp'))
assert d['set_windows_not_verified'] == 0 and d['start_potential_checked_on_every_edge'], d
assert d['start_potential_bound_edges'] <= 231 and d['max_edges'] is not None and d['max_edges'] <= 231, d
EOF
  mv $D/direction_bound_L8_k7_K7_89_19.json.tmp $D/direction_bound_L8_k7_K7_89_19.json
fi
if [ ! -f $D/pipeline_231.generated ]; then
  log "Lean generation"
  nice -n 10 python3 gen_lean_swar.py --index ../data/direction_certificates_k6.json --set ../data/minimal_L8_k7_K7_r3_89_19.json \
    --L 8 --k 7 --K 7 --lam 89/19 --start
  grep -q "theorem upper_231_of_direction_windowsK7R34C7W16" $R/work/spectral/stronger/AggregateDirectionK7R34C7W16Conditional.lean
  # the 230: the same chain plus the certified seven-centre share bound (no window has share sum <= 26,
  # data/share/final_b_X26.jsonl), through the generic ShareBonus module
  DST=$(python3 -c "import json; print(json.load(open('../data/direction_bound_L8_k7_K7_89_19.json'))['start_constant_D'])")
  python3 gen_share_wrapper.py --suffix K7R34C7W16 --L 8 --k 7 --lam 89/19 --D $DST --shapes 132 --lb 27 --bound 230 \
    --outdir $R/work/spectral/stronger
  touch $D/pipeline_231.generated
fi
log "reproduction"
cd $R
nice -n 10 python3 work/spectral/verify_strengthened.py --mathlib-dir $MATHLIB \
  --build-dir work/spectral/.verification/strengthened-k6-resume \
  --core-targets Snake9 PathStructure CubeLocal SquareCounterexample SingletonSquareLemma OptimalityTarget \
  --extra-chains K6R3C7W K6R34C7W K7R34C7W16 --share231 \
  --share-wrappers AggregateDirectionK7R34C7W16Share230 --jobs 2
cp work/spectral/.verification/strengthened-k6-resume/manifest.json outputs/strengthened-direction-231-reproduction-manifest.json
touch $D/pipeline_231.done
log "done"
