#!/bin/bash
# Pilot certificate for one level-116 cube (milestone 39): measures Lean kernel time per LRAT hint at
# literal offset 65,536 and peak RSS.  Run from the repository root of research/unconditional-241.
# Needs: Lean 4.35 at /opt/lean-4.35.0-linux, cadical on PATH, python3.  ~1 h, < 16 GB.
set -e
ROOT=$PWD; M=$ROOT/milestones/39-dim8-lift; L=/opt/lean-4.35.0-linux/bin/lean
W=${PILOT_WORK:-$HOME/pilot39}; mkdir -p $W; HOST=$(hostname)
OUT=$M/cert/results/pilot_$HOST.json; mkdir -p $M/cert/results
log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a $W/pilot.log; }
peak() {  # run a command, print "seconds peakMB" to $W/last
  local s=$(date +%s.%N); "$@" > $W/cmd.out 2>&1 & local P=$!; local m=0 r
  while kill -0 $P 2>/dev/null; do r=$(awk '/VmRSS/{print $2}' /proc/$P/status 2>/dev/null || echo 0)
    for c in $(pgrep -P $P); do r2=$(awk '/VmRSS/{print $2}' /proc/$c/status 2>/dev/null || echo 0); r=$((r + r2)); done
    [ "${r:-0}" -gt $m ] && m=$r; sleep 1; done
  wait $P; local rc=$?; echo "$(echo "$(date +%s.%N) - $s" | bc) $((m / 1024))" > $W/last; return $rc; }
log "1. build the milestone-39 Lean modules (CubeCnf, Export prerequisites)"
bash $M/lean/build.sh > $W/build.log 2>&1
log "2. export the cube CNF (representative 036cbc13bc5243ac, 29 vertices) and solve with LRAT"
(cd $M/lean && LEAN_PATH=build $L --run Export.lean 13 116 036cbc13bc5243ac 29 $W/p0.cnf c4)
s=$(date +%s); cadical -q --lrat --binary=false $W/p0.cnf $W/p0.lrat | head -1 > $W/solve.txt || true; SOLVE=$(( $(date +%s)-s ))
log "   $(cat $W/solve.txt) in $SOLVE s"
log "3. core extraction, variable compaction, packed core module"
python3 $M/cert/pilot.py $W/p0.cnf $W/p0.lrat CubeP0 $W/gen > $W/core.json; cat $W/core.json | tee -a $W/pilot.log
log "4. v3 replay modules (genv3stream, offset 65536)"
python3 $ROOT/lean435/tools/genv3stream.py --work $W/gen --data $W/gen/core --out $W/gen --off 65536 CubeP0 > $W/gen.json
cat $W/gen.json | tee -a $W/pilot.log
log "5. build: LocalWindowModel, LratV3 (4.35 fix), NatPack, ProofPack, SplitZ, core, replay"
R=$W/root; mkdir -p $R/LocalWindowCnf $R/LocalWindowUnsat $R/build/LocalWindowCnf $R/build/LocalWindowUnsat
cp $ROOT/work/final_lean/LocalWindowModel.lean $ROOT/work/final_lean/NatPack.lean $ROOT/work/final_lean/ProofPack.lean $M/cert/SplitZ.lean $R/
sed 's/rw \[Option.mem_toList, Option.mem_def, Option.some.injEq\] at hy/simp only [Option.mem_toList, Option.mem_def, Option.some.injEq] at hy/' \
  $ROOT/work/final_lean/LratV3.lean > $R/LratV3.lean
cp $W/gen/LocalWindowCnf/CubeP0.lean $R/LocalWindowCnf/; cp $W/gen/LocalWindowUnsat/CubeP0.lean $R/LocalWindowUnsat/
cd $R
for m in LocalWindowModel LratV3 NatPack ProofPack SplitZ LocalWindowCnf/CubeP0; do
  LEAN_PATH=build $L --root=. -o build/$m.olean $m.lean > $W/b_$(basename $m).log 2>&1 || { log "FAILED $m"; cat $W/b_$(basename $m).log | head; }
done
log "   building the replay module (all kernel checks happen here)"
set +e
peak env LEAN_PATH=build $L --root=. -o build/LocalWindowUnsat/CubeP0.olean LocalWindowUnsat/CubeP0.lean; RC=$?
set -e
read SEC MB < $W/last; cp $W/cmd.out $W/replay.out
AX=$(grep -o "axioms.*" $W/replay.out | head -1)
printf 'import LocalWindowUnsat.CubeP0\n#print axioms Snake9.LocalWindow.CubeP0.unsat\n' > Ax.lean
AX=$(LEAN_PATH=build $L --root=. Ax.lean 2>&1 | head -2 | tr '\n' ' ')
HINTS=$(python3 -c "import json;print(json.load(open('$W/gen.json'))['hints'])")
python3 - <<PY
import json
r = dict(host="$HOST", exit_code=$RC, replay_seconds=float("$SEC"), replay_peak_rss_mb=int("$MB"), hints=int("$HINTS"),
         ms_per_hint=1000.0 * float("$SEC") / int("$HINTS"), solve_seconds=$SOLVE, axioms="""$AX""",
         core=json.load(open("$W/core.json")), gen=json.load(open("$W/gen.json")),
         replay_errors=open("$W/replay.out").read()[-2000:])
json.dump(r, open("$OUT", "w"), indent=1); print(json.dumps(r))
PY
log "6. commit the result"
cd $ROOT
git add $OUT && git commit -qm "milestone 39: pilot certificate measurement ($HOST)" && \
for i in 1 2 3 4; do git fetch -q origin research/unconditional-241 && git merge -q --no-edit FETCH_HEAD && git push -q origin HEAD:research/unconditional-241 && break; sleep $((i*15)); done
log "done: $(cat $OUT | head -8)"
