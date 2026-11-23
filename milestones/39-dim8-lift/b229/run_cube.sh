#!/bin/bash
# run_cube.sh HEX K SKIP_PARENT(0/1) : B229 one-level manual split study for one cube (steps A+B)
set -u
H=$1; K=$2; SKIP=$3; O=/home/user/b229/$H; mkdir -p $O/child $O/probe; cd /home/user/Snake-in-the-box-in-9/milestones/39-dim8-lift/lean
h=$(echo $H | tr A-F a-f)
LEAN_PATH=$PWD/build python3 /home/user/b229/meas.py export $O/timing.jsonl -- /opt/lean-4.35.0-linux/bin/lean --run Export.lean 13 116 $h $K $O/parent.cnf q
cd $O
awk 'NR>=2 && NR<=65' parent.cnf > C.units; awk 'NR>65' parent.cnf > F.body
sha256sum parent.cnf C.units F.body > hashes.txt; head -1 parent.cnf >> hashes.txt
python3 /home/user/b229/meas.py up_parent timing.jsonl -- sh -c "/home/user/b229/up parent.cnf parent > up_parent.txt 2> up_parent.err"
python3 - <<'PY'
occ={int(a):int(b) for _,a,b in (l.split() for l in open('up_parent.txt') if l.startswith('OCC'))}
sv=sorted(((occ.get(v,0),v) for v in range(65,257) if v in occ), reverse=True)[:16]
open('cand16','w').write(' '.join(str(v) for c,v in sv))
PY
python3 /home/user/b229/meas.py up_probe16 timing.jsonl -- sh -c "/home/user/b229/up parent.cnf probe $(cat cand16) > probe16.jsonl 2> probe16.err"
python3 - <<'PY'
import json
r=[json.loads(l) for l in open('probe16.jsonl')]; par=r[0]; r=r[1:]
rows=[]
for i in range(0,len(r),2):
    p,n=r[i],r[i+1]; v=int(p['tag'])
    closed=p['conflict'] or n['conflict']
    hardrem=max(x['rem_clauses'] for x in (p,n) if not x['conflict']) if not (p['conflict'] and n['conflict']) else 0
    rows.append((0 if closed else 1, hardrem, v))
rows.sort(); top=[v for _,_,v in rows[:4]]
open('top4','w').write(' '.join(map(str,top)))
json.dump(dict(parent=par, ranking=rows), open('ranking.json','w'))
PY
for v in $(cat top4); do for s in "" "-"; do python3 /home/user/b229/mkchild.py parent.cnf child/x${s:-+}$v.cnf ${s}$v; done; done > children.jsonl
L=""; [ "$SKIP" = 0 ] && L="parent"; for v in $(cat top4); do L="$L +$v -$v"; done
echo $L | tr ' ' '\n' | grep . | xargs -P 3 -I{} sh -c 'if [ {} = parent ]; then f=parent.cnf; else f=child/x{}.cnf; fi; bash /home/user/b229/probe.sh '$O' {} $f 45' > probe_status.txt 2>/dev/null
echo "CUBE DONE $H"
