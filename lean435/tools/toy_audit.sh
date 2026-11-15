#!/bin/bash
# Step 4 of the 4.35 port: build the 6SC toy chain of milestone 35 (two real ctx certificates,
# Snake9.upper_254_toy6SC) as worker, then run the interface-only final audit, then show that a
# bad certificate (sorry / native_decide / extra axiom) is caught by the axiom whitelist.
#
#   bash lean435/tools/toy_audit.sh [WORKDIR]      (default ~/l435/toy)
#
# WORKDIR/worker   build of everything (the "worker" machine), manifest worker.jsonl
# WORKDIR/iface    the public .olean files the worker publishes (certificates, bridge, aggregate)
# WORKDIR/spec     the auditor's own rebuild of the spec/support layer from source
# WORKDIR/audit*   clean directories of the final runs (only hard links to public .olean files)
set -euo pipefail
R=$(cd "$(dirname "$0")/../.." && pwd)
T="$R/lean435/tools"
W=${1:-$HOME/l435/toy}
mkdir -p "$W"
W=$(cd "$W" && pwd)
SRC="$R/lean435/src"
B="python3 $T/build.py --jobs ${JOBS:-3}"
CERTS="LocalWindowCtxUnsat.C70123412A236664K15 LocalWindowCtxUnsat.C801234032A544643K15"
WORKER_MODS="$CERTS DirectionWindowBridge6SCToy AggregateDirection6SCToy"
THMS="Snake9.LocalWindow.TagsSW.soundSC Snake9.LocalWindow.refuted_share_from_dir
 Snake9.DirectionWindow6SC.ctxOK7_of_refuted Snake9.DirectionWindow6SC.ctxOK8_of_refuted
 Snake9.DirectionWindow6SC.ctx_windows6SC Snake9.WindowAutomaton.total_bound6SC
 Snake9.WindowAutomaton.check6SCAt_of_W Snake9.upper_of_refuted6SC
 Snake9.DirectionWindow6SC.ctx7_C70123412A236664K15 Snake9.DirectionWindow6SC.ctx8_C801234032A544643K15
 Snake9.DirectionWindow6SC.label6SCToy Snake9.upper_254_toy6SC"

echo "== port"
python3 "$T/port.py" $(cat "$R/lean435/core-roots.txt") $CERTS AggregateDirection6SCToy

echo "== worker build"
t0=$(date +%s)
$B --src "$SRC" --build "$W/worker" AggregateDirection6SCToy | tail -3
echo "worker build: $(( $(date +%s) - t0 )) s"

# modules of the closure that are ours (not mathlib/core), and the spec layer = those not above a certificate
python3 - "$SRC" "$W" $WORKER_MODS <<'EOF'
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(sys.argv[1]), 'tools'))
import build
src, w, worker = sys.argv[1], sys.argv[2], set(sys.argv[3:])
seen, order = set(), []
def go(m):
    if m in seen: return
    seen.add(m)
    p = os.path.join(src, m.replace('.', '/') + '.lean')
    if not os.path.exists(p): return
    for d in build.header_imports(p): go(d)
    order.append(m)
go('AggregateDirection6SCToy')
open(os.path.join(w, 'all.txt'), 'w').write('\n'.join(order) + '\n')
spec = [m for m in order if m not in worker and not m.startswith(('LocalWindowCtxCnf.', 'LocalWindowCtxUnsat.'))]
open(os.path.join(w, 'spec.txt'), 'w').write('\n'.join(spec) + '\n')
print(f'closure: {len(order)} repository modules, spec layer {len(spec)}')
EOF

echo "== worker manifest + publish"
rm -f "$W/worker.jsonl"; rm -rf "$W/iface"
python3 "$T/audit.py" manifest --src "$SRC" --build "$W/worker" --out "$W/worker.jsonl" $(cat "$W/all.txt")
python3 "$T/audit.py" publish --build "$W/worker" --manifest "$W/worker.jsonl" --iface "$W/iface" $WORKER_MODS
ls -l "$W"/iface/*.olean "$W"/iface/*/*.olean | awk '{print $5, $9}'

echo "== auditor: rebuild of the spec layer from source"
t0=$(date +%s)
$B --src "$SRC" --build "$W/spec" $(cat "$W/spec.txt") | tail -2
echo "spec rebuild: $(( $(date +%s) - t0 )) s"

cat > "$W/Audit6SC435.lean" <<'EOF'
module
import AggregateDirection6SCToy
EOF
for t in $THMS; do echo "#print axioms $t" >> "$W/Audit6SC435.lean"; done
TA=""; for t in $THMS; do TA="$TA --theorem $t"; done

echo "== final audit (good chain)"
python3 "$T/audit.py" final --src "$SRC" --spec-build "$W/spec" --iface "$W/iface" --manifest "$W/worker.jsonl" \
  --require-spec-manifest --final "$W/Audit6SC435.lean" $TA --work "$W/audit" | tee "$W/audit.txt"

# ---- bad certificates: the worker cheats in the ctx 7 certificate
bad() {  # name, python transformation of the replay source
  local n=$1 code=$2
  local S="$W/bad-$n/src" BB="$W/bad-$n/worker"
  rm -rf "$W/bad-$n"; mkdir -p "$W/bad-$n"
  cp -r "$SRC" "$S"
  cp -al "$W/worker" "$BB"      # hard links; build.py deletes a module's parts before rebuilding it
  python3 - "$S/LocalWindowCtxUnsat/C70123412A236664K15.lean" "$code" <<'EOF'
import sys
p, code = sys.argv[1], sys.argv[2]
s = open(p).read()
ok = 'theorem ok0 : '
i = s.index(ok); j = s.index(':= by\n  decide +kernel\n', i)
if code == 'sorry':
    s = s[:j] + ':= by\n  sorry\n' + s[j + len(':= by\n  decide +kernel\n'):]
elif code == 'axiom':
    s = s[:i] + 'axiom cheat : False\n\n' + s[i:j] + ':= cheat.elim\n' + s[j + len(':= by\n  decide +kernel\n'):]
elif code == 'native':
    s = s[:i] + 'theorem hoff_nd : 0 < 2400 := by native_decide\n\n' + s[i:]
    assert s.count('have hoff : 0 < 2400 := by decide') == 1
    s = s.replace('have hoff : 0 < 2400 := by decide', 'have hoff : 0 < 2400 := hoff_nd')
open(p, 'w').write(s)
EOF
  $B --allow-sorry --src "$S" --build "$BB" AggregateDirection6SCToy | tail -2
  python3 "$T/audit.py" manifest --src "$S" --build "$BB" --out "$W/bad-$n/worker.jsonl" $(cat "$W/all.txt")
  python3 "$T/audit.py" publish --build "$BB" --manifest "$W/bad-$n/worker.jsonl" --iface "$W/bad-$n/iface" $WORKER_MODS
  echo "== final audit (bad certificate: $n); must FAIL"
  if python3 "$T/audit.py" final --src "$SRC" --spec-build "$W/spec" --iface "$W/bad-$n/iface" \
       --manifest "$W/bad-$n/worker.jsonl" --require-spec-manifest --final "$W/Audit6SC435.lean" $TA \
       --work "$W/bad-$n/audit" > "$W/bad-$n/audit.txt"; then
    cat "$W/bad-$n/audit.txt"; echo "BAD CERTIFICATE ($n) NOT CAUGHT"; exit 1
  fi
  grep -E "upper_254_toy6SC|AUDIT|NOT IN" "$W/bad-$n/audit.txt" | grep -v "^'" || true
  echo "bad certificate ($n): caught"
}
bad sorry sorry
bad native native
bad axiom axiom
echo "TOY AUDIT DEMONSTRATION COMPLETE"
