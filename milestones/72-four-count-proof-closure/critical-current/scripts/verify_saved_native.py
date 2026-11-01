"""Check an already generated native proof without rerunning its solver."""
from pathlib import Path
from collections import Counter
import hashlib,json,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
import gen_lean_sat as gen
tag=sys.argv[1];limit=int(sys.argv[2]) if len(sys.argv)>2 else 180
f=HERE/f'data/{tag}-certificate.json';meta=json.loads(f.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cnf=HERE/f'build/{tag}.cnf';drat=HERE/f'build/{tag}.drat';core=HERE/f'build/{tag}.core.cnf'
assert sha(cnf)==meta['cnf_sha256'] and sha(drat)==meta['drat_sha256']
previous=meta['status'];start=time.monotonic()
log=HERE/f'logs/{tag}-verify.log'
try:
 with log.open('w') as out:
  r=subprocess.run([str(ROOT/'work/share-wheels/drat-trim.exe'),str(cnf),str(drat),'-c',str(core),'-t',str(limit)],stdout=out,stderr=subprocess.STDOUT,timeout=limit+30)
 meta['verify_exit']=r.returncode
 if r.returncode==0 and 's VERIFIED' in log.read_text():
  e=TaggedShare(meta['directions'],meta['bounds'],meta['cap'])
  for c in meta.get('cycle_cuts',[]):
   assert gen.is_cycle_set(c);e.add([-e.var[v] for v in c],('old',('cut',)))
  lookup={tuple(sorted(c)):t for c,t in zip(e.clauses,e.tags)}
  tags=[lookup[tuple(sorted(map(int,l.split()[:-1])))][0] for l in core.read_text().splitlines() if l and l[0] not in 'pc']
  meta.update(status='NATIVE_DRAT_VERIFIED',core_sha256=sha(core),core_clause_tags=dict(Counter(tags)))
 else:meta['status']='DRAT_VERIFY_INCOMPLETE'
except subprocess.TimeoutExpired:meta['status']='DRAT_VERIFY_TIMEOUT'
meta.setdefault('verification_attempts',[]).append(dict(previous_status=previous,requested_seconds=limit,seconds=time.monotonic()-start,status=meta['status']))
f.write_text(json.dumps(meta,indent=2)+'\n')
print(meta['status'],tag,meta['verification_attempts'][-1],flush=True)
