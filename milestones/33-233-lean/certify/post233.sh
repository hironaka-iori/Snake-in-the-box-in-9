#!/usr/bin/env bash
# Post-production steps of the unconditional 233 (CERT-PROGRESS.md, "Projection", "Then:").
# Run only after `prod233.py` has logged {"done": "all certificates built"} and exited.
#
#   CERT233_SCR=/home/user/cert233work bash milestones/33-233-lean/certify/post233.sh
#
# Steps (each aborts the script on failure; the whole run is logged to $CERT233_SCR/logs/post233.log):
#   0. preconditions: no prod/pregen/guarded build running, free disk, every certificate built
#      (`cert233.py status`: seeds and share keys, Cnf and replay .olean);
#   1. `cert233.py final` into a scratch directory first; the 30 modules must be byte-identical to
#      the ones in work/final_lean (written 10 Nov 14:38), so the real `final` is a no-op and the
#      built chunks LocalWindowDirUnsatN6SB233_10..13, LocalWindowDirKeys*6SB233 and
#      LocalWindowDirUnsatR6SB233 keep their mtimes (FORCE_FINAL=1 continues past a difference);
#      then the real `final` (it only rewrites files whose text changed) and an mtime check;
#   2. staleness simulation of the closure of the two aggregates (guarded_lake_build's own
#      closure()/uptodate() with --trust-mtime): only the 23 expected modules may be stale;
#   3. guarded build (--direct --trust-mtime --no-ilean; lean binary $LEAN_BIN, default the toolchain's,
#      e.g. LEAN_BIN=/home/user/leanbig.sh for `ulimit -s unlimited; lean -s 1048576`) of LocalWindowDirUnsat6SB233 and
#      LocalWindowShareUnsat6SB233; their `#print axioms` lines are checked;
#   4. floors overlay (symlinks) in a NEW directory; the two port top-level .olean files that the core
#      also has (byte-identical copies, `cp -p` of 10 Nov) are removed from it, otherwise
#      chain_audit.py refuses the extra path ("would shadow");
#   5. chain_audit.py --target UpperBound233 --reuse --extra-lean-path NEWDIR; prints the axioms.
set -euo pipefail

ROOT=/home/user/Snake-in-the-box-in-9
export CERT233_SCR=${CERT233_SCR:-/home/user/cert233work}
LEANBIN=/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin
MATHLIB=/home/user/lean-deps/mathlib4
LEAN=$ROOT/work/final_lean
LIB=$LEAN/.lake/build/lib/lean
CHAIN=$ROOT/work/spectral/.verification/chain
CERT=$ROOT/milestones/33-233-lean/certify/cert233.py
GLB=$ROOT/work/guarded_lake_build.py
PORT=/home/user/floors233/.lake/build/lib/lean
NEWDIR=${NEWDIR:-/home/user/floors233-lp-final}
AUDIT_LOG=outputs/upper-bound-233-audit-linux.log      # relative to $ROOT (chain_audit opens it there)
GLOG=$LEAN/.lake/guarded_build_233final.jsonl
MIN_DISK_MB=${MIN_DISK_MB:-2000}   # 1.5 GB floor + ~0.15 GB overlay + aggregates/audit + margin
LOG=$CERT233_SCR/logs/post233.log
export PATH=$LEANBIN:$PATH

mkdir -p "$CERT233_SCR/logs"
exec > >(tee -a "$LOG") 2>&1
echo "=== post233.sh start $(date -u +%FT%TZ)"

free_mb() { df -Pm / | awk 'NR==2 {print $4}'; }
need_disk() {
  local f; f=$(free_mb)
  echo "free disk: $f MB (need >= $1 MB)"
  if [ "$f" -lt "$1" ]; then echo "ABORT: not enough free disk"; exit 1; fi
}

# ---------------------------------------------------------------- 0. preconditions
if pgrep -f 'prod233\.py|pregen233\.py|guarded_lake_build\.py|cert233\.py (cores|cnf|replay)' >/dev/null; then
  echo "ABORT: production processes still running:"; pgrep -af 'prod233\.py|pregen233\.py|guarded_lake_build\.py|cert233\.py' || true
  exit 1
fi
if ! tail -n 1 "$ROOT/milestones/33-233-lean/certify/data/prod6SB233.jsonl" | grep -q '"done"'; then
  echo "WARNING: last line of prod6SB233.jsonl is not {\"done\": ...}; relying on the status counts below"
fi
need_disk "$MIN_DISK_MB"
[ -x "$LEANBIN/lean" ] && [ -x "$LEANBIN/lake" ] || { echo "ABORT: no lean/lake in $LEANBIN"; exit 1; }
[ "$(git -C "$MATHLIB" rev-parse HEAD)" = c44e0c8ee63ca166450922a373c7409c5d26b00b ] || { echo "ABORT: mathlib pin"; exit 1; }
[ -d "$PORT/LocalWindowCnf" ] || { echo "ABORT: no floors port at $PORT"; exit 1; }
[ ! -e "$NEWDIR" ] || { echo "ABORT: $NEWDIR exists (floors_overlay.py needs a new directory; set NEWDIR=...)"; exit 1; }

echo "--- cert233.py status"
python3 "$CERT" status | tee "$CERT233_SCR/post233_status.json"
python3 - "$CERT233_SCR/post233_status.json" <<'EOF'
import json, sys
r = json.load(open(sys.argv[1]))
tot = r['seeds'] + r['share']
built = r['seed_unsat_built'] + r['share_unsat_built']
print(f"certificates: {built} / {tot} replay .olean ({r['seed_unsat_built']}/{r['seeds']} seeds, "
      f"{r['share_unsat_built']}/{r['share']} share); Cnf {r['seed_cnf_built']}/{r['seeds']}, {r['share_cnf_built']}/{r['share']}")
ok = (r['seed_unsat_built'] == r['seed_cnf_built'] == r['seeds'] and
      r['share_unsat_built'] == r['share_cnf_built'] == r['share'] and
      r['cores_plain'] == r['new_plain'] + r['h8'] and r['cores_share'] == r['share'])
if not ok:
    sys.exit('ABORT: not every certificate is built')
EOF

# ---------------------------------------------------------------- 1. final
echo "--- 1. cert233.py final (dry run into scratch, then in place)"
FC=$(mktemp -d "$CERT233_SCR/final_check.XXXXXX")
python3 "$CERT" final --out "$FC" | tee "$FC/final.out"
grep -q '; 0 certificate replays not generated or built yet' "$FC/final.out" || { echo "ABORT: final reports missing certificates"; exit 1; }
ndiff=0
for f in "$FC"/*.lean; do
  b=$(basename "$f")
  if ! cmp -s "$f" "$LEAN/$b"; then echo "  differs from work/final_lean: $b"; ndiff=$((ndiff + 1)); fi
done
echo "final dry run: $(ls "$FC"/*.lean | wc -l) modules, $ndiff differ from work/final_lean"
if [ "$ndiff" -ne 0 ] && [ "${FORCE_FINAL:-0}" != 1 ]; then
  echo "ABORT: final would rewrite $ndiff modules (they and their dependents would be rebuilt); inspect $FC, rerun with FORCE_FINAL=1 to accept"
  exit 1
fi
KEEP="LocalWindowDirKeys6SB233 LocalWindowDirKeysN6SB233 LocalWindowDirKeysR6SB233 LocalWindowDirUnsatR6SB233 LocalWindowDirUnsatN6SB233_10 LocalWindowDirUnsatN6SB233_11 LocalWindowDirUnsatN6SB233_12 LocalWindowDirUnsatN6SB233_13"
before=$(for m in $KEEP; do stat -c '%Y %n' "$LEAN/$m.lean"; done)
python3 "$CERT" final
after=$(for m in $KEEP; do stat -c '%Y %n' "$LEAN/$m.lean"; done)
if [ "$before" != "$after" ] && [ "${FORCE_FINAL:-0}" != 1 ]; then
  echo "ABORT: final touched built modules:"; diff <(echo "$before") <(echo "$after") || true; exit 1
fi
grep -lE 'sorry|native_decide|^axiom' "$LEAN"/LocalWindowDir*6SB233*.lean "$LEAN"/LocalWindowShareUnsat6SB233*.lean \
  "$ROOT/work/spectral/stronger/UpperBound233.lean" && { echo "ABORT: sorry/native_decide/axiom in a generated module"; exit 1; } || true
rm -rf "$FC"

# ---------------------------------------------------------------- 2. staleness simulation
echo "--- 2. staleness simulation (guarded_lake_build closure/uptodate, --trust-mtime)"
python3 -I - "$GLB" "$LEAN" <<'EOF'
import importlib.util, sys
from pathlib import Path
spec = importlib.util.spec_from_file_location('glb', sys.argv[1])
g = importlib.util.module_from_spec(spec); spec.loader.exec_module(g)
g.ROOT = Path(sys.argv[2])
deps = g.closure(['LocalWindowDirUnsat6SB233', 'LocalWindowShareUnsat6SB233'], True)
st = {}
def s(m):
    if m not in st:
        st[m] = any(s(d) for d in deps[m]) or not g.uptodate(m, deps[m])
    return st[m]
for m in deps:
    s(m)
stale = sorted(m for m in deps if st[m])
expected = ({'LocalWindowDirUnsat6SB233', 'LocalWindowShareUnsat6SB233'}
            | {f'LocalWindowDirUnsatN6SB233_{c}' for c in (*range(10), 14)}
            | {f'LocalWindowShareUnsat6SB233_{c}' for c in range(10)})
bad = [m for m in stale if m not in expected]
print(f'closure {len(deps)} modules ({len(g.PREBUILT)} prebuilt .olean without source); stale {len(stale)}:', stale)
if bad:
    sys.exit(f'ABORT: stale modules outside the expected 23 (would be recompiled): {bad[:30]}')
EOF

# ---------------------------------------------------------------- 3. guarded build of the aggregates
echo "--- 3. guarded build of LocalWindowDirUnsat6SB233 and LocalWindowShareUnsat6SB233"
need_disk 1700
t0=$(date +%s)
( cd "$LEAN" && LEAN_PATH=$CHAIN nice -n 10 python3 "$GLB" --root "$LEAN" --direct --trust-mtime --no-ilean \
    --lean "${LEAN_BIN:-$LEANBIN/lean}" \
    --jobs 3 --heavy '^LocalWindow(DirUnsat|ShareUnsat)6SB233$' --heavy-jobs 1 \
    --rss-cap-gb 10 --min-free-gb 4 --floor-gb 1.5 --min-disk-mb 1500 \
    --log "$GLOG" LocalWindowDirUnsat6SB233 LocalWindowShareUnsat6SB233 )
echo "guarded build: $(( $(date +%s) - t0 )) s"
for m in LocalWindowDirUnsat6SB233 LocalWindowShareUnsat6SB233; do
  [ -f "$LIB/$m.olean" ] || { echo "ABORT: $m.olean missing"; exit 1; }
  ax=$(grep -h "depends on axioms" "$LEAN/.lake/guarded_logs/$m.log" || true)
  echo "$m: $ax"
  [ -n "$ax" ] && ! echo "$ax" | grep -qvE "depends on axioms: \[((propext|Classical\.choice|Quot\.sound)(, )?)*\]$" \
    || { echo "ABORT: unexpected axioms in $m"; exit 1; }
done
grep -E '"module": "LocalWindow(DirUnsat|ShareUnsat)6SB233(_[0-9]+)?"|"module": "LocalWindowDirUnsatN6SB233_[0-9]+"' "$GLOG" | grep -v uptodate | tail -25 || true

# ---------------------------------------------------------------- 4. floors overlay
echo "--- 4. floors overlay into $NEWDIR"
need_disk 1700
python3 -I "$ROOT/milestones/33-233-lean/scripts/floors_overlay.py" "$PORT" "$NEWDIR"
# the core holds byte-identical copies of these two port modules; a symlink to the port file would make
# chain_audit.py stop with "would shadow"; without it Lean finds the core copy
for f in LocalWindowTagsShare.olean LocalWindowTagsSharePacked.olean; do
  if [ -e "$LIB/$f" ]; then
    cmp -s "$PORT/$f" "$LIB/$f" || { echo "ABORT: $f differs between the port and the core"; exit 1; }
    rm "$NEWDIR/$f"; echo "removed overlay link $f (core copy is identical)"
  fi
done
nd=$(find "$NEWDIR" -xtype l | wc -l)
echo "overlay: $(find "$NEWDIR" -type l | wc -l) symlinks, $nd dangling, $(du -sm "$NEWDIR" | cut -f1) MB"
[ "$nd" -eq 0 ] || { echo "ABORT: dangling links in the overlay"; exit 1; }
python3 -I - "$NEWDIR" "$LIB" "$CHAIN" <<'EOF'
import sys
from pathlib import Path
d, core, chain = map(Path, sys.argv[1:])
bad = [str(f) for f in d.rglob('*.olean') for q in (core / f.relative_to(d), chain / f.relative_to(d))
       if q.exists() and q.resolve() != f.resolve()]
if bad:
    sys.exit(f'ABORT: overlay would shadow {len(bad)} files, e.g. {bad[:5]}')
print('shadow check (as chain_audit.py): ok')
EOF

# ---------------------------------------------------------------- 5. chain audit
echo "--- 5. chain_audit.py --target UpperBound233"
need_disk 1600
cd "$ROOT"
t0=$(date +%s)
set +e
python3 work/spectral/chain_audit.py --mathlib-dir "$MATHLIB" --target UpperBound233 --reuse \
  --extra-lean-path "$NEWDIR" --log "$AUDIT_LOG" \
  --axioms Snake9.upper_bound_233 Snake9.verified_interval_191_233
rc=$?
set -e
echo "chain audit: exit $rc, $(( $(date +%s) - t0 )) s"
echo "=== axioms ($AUDIT_LOG, this run):"
tail -n 12 "$AUDIT_LOG" | grep -E "depends on axioms|AXIOM AUDIT|FAILED|chain wall" || true
echo "free disk at end: $(free_mb) MB"
echo "=== post233.sh end $(date -u +%FT%TZ): $([ $rc -eq 0 ] && echo 'AXIOM AUDIT PASSED' || echo 'AXIOM AUDIT FAILED')"
exit $rc
