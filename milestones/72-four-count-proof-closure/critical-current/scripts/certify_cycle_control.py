"""Native certificate for a count-free shape; geometric Lean replay is separate."""
from pathlib import Path
import collections,hashlib,json,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cap=int(sys.argv[2]) if len(sys.argv)>2 else 11
solve_seconds=float(sys.argv[3]) if len(sys.argv)>3 else 60
index=int(sys.argv[1])
shapes=read(HERE/'data/all-six-direction-shapes.json')['up_to_reversal']
assert index==3 and cap==15
row=dict(directions=shapes[index],counts=[6]*5);prior=dict(cycle_cuts=read(HERE/'data/cap15-cyclic-control.json')['cycles'])
bounds=[(0,21)]*5
start=time.monotonic();enc=TaggedShare(row['directions'],bounds,cap)
tag=f'general{index}-cap{cap}-cycles';cert=HERE/'build'/tag;cert.parent.mkdir(exist_ok=True)
import gen_lean_sat as gen
for cycle in prior['cycle_cuts']:
    assert gen.is_cycle_set(cycle)
    enc.add([-enc.var[v] for v in cycle],('old',('cut',)))
cnf=cert.with_suffix('.cnf');drat=cert.with_suffix('.drat');core=cert.with_suffix('.core.cnf')
with cnf.open('w') as f:
    f.write(f'p cnf {enc.nv} {len(enc.clauses)}\n')
    for clause in enc.clauses:f.write(' '.join(map(str,clause))+' 0\n')
meta=dict(cycle_cuts=prior['cycle_cuts'],shape_index=index,directions=row['directions'],bounds=bounds,cap=cap,variables=enc.nv,clauses=len(enc.clauses),cnf_sha256=sha(cnf),solve_seconds=solve_seconds,scope='Native CNF certificate only. A universal share theorem requires checked geometric interpretation and Lean replay.')
(HERE/'logs').mkdir(exist_ok=True)
commands=[('solve',[r'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin\cadical.exe','-q','--no-binary',str(cnf),str(drat)],20),('verify',[str(ROOT/'work/share-wheels/drat-trim.exe'),str(cnf),str(drat),'-c',str(core)],0)]
for name,cmd,expected in commands:
    try:
        r=subprocess.run(cmd,capture_output=True,text=True,timeout=solve_seconds if name=='solve' else 60)
        (HERE/f'logs/{tag}-{name}.log').write_text(r.stdout+r.stderr)
        meta[name+'_exit']=r.returncode
        if r.returncode!=expected:
            meta['status']=name.upper()+'_INCOMPLETE'
            if name=='solve' and r.returncode==10:
                vals=[int(x) for line in r.stdout.splitlines() if line.startswith('v ') for x in line.split()[1:]]
                positive={x for x in vals if x>0}
                assert all(any((x>0)==(abs(x) in positive) for x in cl) for cl in enc.clauses)
                meta.update(status='SAT_LOCAL_RELAXATION',selected=sorted(v for v in enc.ball if enc.var[v] in positive))
            break
        if name=='verify':
            assert 's VERIFIED' in r.stdout
            lookup={tuple(sorted(c)):tag for c,tag in zip(enc.clauses,enc.tags)}
            tags=[]
            for line in core.read_text().splitlines():
                if line and not line.startswith(('p','c')):tags.append(lookup[tuple(sorted(map(int,line.split()[:-1])))][0])
            meta.update(status='NATIVE_DRAT_VERIFIED',core_clause_tags=dict(collections.Counter(tags)),core_sha256=sha(core),drat_sha256=sha(drat))
    except subprocess.TimeoutExpired:
        meta['status']=name.upper()+'_TIMEOUT';break
meta['seconds']=time.monotonic()-start
(HERE/f'data/{tag}-certificate.json').write_text(json.dumps(meta,indent=2)+'\n');print(meta,flush=True)
