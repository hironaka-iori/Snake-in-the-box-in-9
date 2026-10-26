"""Native certificate for the most frequent witness-supported critical window."""
from pathlib import Path
import argparse,gzip,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
ap=argparse.ArgumentParser();ap.add_argument('--row',type=int,default=0);args=ap.parse_args()
row=json.loads((HERE/'data/windows.json').read_text())[args.row]
bounds=[[6,21] if c==6 else [c,c] for c in row['counts']];cap=95;name=f'obstruction{args.row}_95';prefix=HERE/'certificates'/name;prefix.parent.mkdir(exist_ok=True)
t=time.monotonic();enc=TaggedShare(row['directions'],bounds,cap)
full=prefix.with_suffix('.full.cnf');full.write_text(f'p cnf {enc.nv} {len(enc.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in enc.clauses))
with gzip.open(prefix.with_suffix('.meanings.json.gz'),'wt') as f:json.dump(dict(meaning=enc.meaning,smeaning=enc.smeaning,ctrs=enc.ctrs,tots=enc.tots,tags=enc.tags),f)
print('Encoded',enc.nv,'variables',len(enc.clauses),'clauses',flush=True)
with (HERE/f'logs/{name}-cadical.txt').open('w') as log:
 try:r=subprocess.run([str(BIN/'cadical.exe'),'-q','--no-binary',str(full),str(prefix.with_suffix('.drat'))],stdout=log,stderr=subprocess.STDOUT,timeout=240);code=r.returncode
 except subprocess.TimeoutExpired:code=None
meta=dict(name=name,directions=row['directions'],counts=row['counts'],bounds=bounds,cap=cap,window=enc.window,variables=enc.nv,clauses=len(enc.clauses),solver_exit=code,seconds=time.monotonic()-t)
if code==20:
 with (HERE/f'logs/{name}-drat-check.txt').open('w') as log:
  r=subprocess.run([str(ROOT/'work/share-wheels/drat-trim.exe'),str(full),str(prefix.with_suffix('.drat')),'-c',str(prefix.with_suffix('.core.cnf'))],stdout=log,stderr=subprocess.STDOUT,timeout=240)
 assert r.returncode==0 and 's VERIFIED' in (HERE/f'logs/{name}-drat-check.txt').read_text()
 core=[list(map(int,l.split()))[:-1] for l in prefix.with_suffix('.core.cnf').read_text().splitlines() if l and not l.startswith(('c','p'))]
 lookup={tuple(sorted(c)):i for i,c in enumerate(enc.clauses)};ids=[lookup[tuple(sorted(c))] for c in core];families={}
 for i in ids:k=enc.tags[i][0];families[k]=families.get(k,0)+1
 meta.update(status='NATIVE_VERIFIED_UNSAT',core_clauses=len(core),source_original_clause_ids=[i+1 for i in ids],families=families,scope='DRAT checked; Lean replay and geometric interpretation still pending.')
else:meta.update(status='SAT' if code==10 else 'UNKNOWN',scope='No exclusion certificate established.')
(HERE/f'data/{name}.json').write_text(json.dumps(meta,indent=2)+'\n');print({k:v for k,v in meta.items() if k!='source_original_clause_ids'},flush=True)
