"""Native certificate attempt for w000 share >=96; geometric Lean replay remains pending."""
from pathlib import Path
import collections,hashlib,json,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cap=int(sys.argv[1]) if len(sys.argv)>1 else 95
row=read(HERE/'data/windows.json')[2];prior=read(HERE/'data/probes/w002-None.json');assert prior['status']=='SAT'
bounds=[(6,21) if c==6 else (c,c) for c in row['counts']]
start=time.monotonic();enc=TaggedShare(row['directions'],bounds,cap)
tag=f'share2-cap{cap}';cert=HERE/'build'/tag;cert.parent.mkdir(exist_ok=True)
for cycle in prior['cycle_cuts']:enc.add([-enc.var[v] for v in cycle],('old',('cut',)))
cnf=cert.with_suffix('.cnf');drat=cert.with_suffix('.drat');core=cert.with_suffix('.core.cnf')
with cnf.open('w') as f:
    f.write(f'p cnf {enc.nv} {len(enc.clauses)}\n')
    for clause in enc.clauses:f.write(' '.join(map(str,clause))+' 0\n')
meta=dict(window=2,directions=row['directions'],bounds=bounds,cap=cap,variables=enc.nv,clauses=len(enc.clauses),cnf_sha256=sha(cnf),scope='Native CNF certificate only. A universal share theorem requires checked geometric interpretation and Lean replay.')
(HERE/'logs').mkdir(exist_ok=True)
commands=[('solve',[r'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin\cadical.exe','-q','--no-binary',str(cnf),str(drat)],20),('verify',[str(ROOT/'work/share-wheels/drat-trim.exe'),str(cnf),str(drat),'-c',str(core)],0)]
for name,cmd,expected in commands:
    try:
        r=subprocess.run(cmd,capture_output=True,text=True,timeout=60)
        (HERE/f'logs/{tag}-{name}.log').write_text(r.stdout+r.stderr)
        meta[name+'_exit']=r.returncode
        if r.returncode!=expected:meta['status']=name.upper()+'_INCOMPLETE';break
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
