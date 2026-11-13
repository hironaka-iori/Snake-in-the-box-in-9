"""Place each saved48-edge parent against the published50-edge parent."""
from pathlib import Path
import collections,hashlib,itertools,json,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
dest=H/'data/mixed51-49.json';assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=H/'data/parents48-keep24.json';raw=source.read_bytes();parents=json.loads(raw)['parents']
baseline=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json';p=json.loads(baseline.read_bytes())['7']['vertices']
start=time.monotonic();rows=[];witness=None;samples=[];status='COMPLETE'
for i,parent in enumerate(parents):
 q=parent['vertices'];hist=collections.Counter();best=128;examples=[];done=0
 for perm in itertools.permutations(range(7)):
  images=[sum(((v>>k)&1)<<perm[k] for k in range(7)) for v in q];counts=[0]*128
  for u in p:
   for v in images:counts[u^v]+=1
  hist.update(counts);done+=1;local=min(counts)
  if local<best:best=local;examples=[]
  if local==best and len(examples)<8:
   examples.extend(dict(permutation=list(perm),translation=t) for t,c in enumerate(counts) if c==best);examples=examples[:8]
  if local==0:
   t=counts.index(0);paths=[p,[128+(v^t) for v in images]]
   assert len(set(paths[0]+paths[1]))==len(p)+len(q)
   assert all((u^v).bit_count()!=1 for u in paths[0] for v in paths[1])
   for path in paths:assert all(((u^path[b]).bit_count()==1)==(b==a+1) for a,u in enumerate(path) for b in range(a+1,len(path)))
   witness=dict(parent=i,permutation=list(perm),translation=t,paths=paths,fixed_face_vertices=len(p)+len(q));status='WITNESS';break
  if done%128==0:
   snap=snapshot();samples.append(snap)
   if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:status='RESOURCE_LIMIT';break
   if time.monotonic()-start>90:status='TIME_LIMIT';break
 rows.append(dict(parent=i,permutations=done,isometries=128*done,minimum_intersection=best,minimum_examples=examples,intersection_histogram=dict(sorted(hist.items()))))
 if status!='COMPLETE':break
out=dict(status=status,seconds=time.monotonic()-start,parents=len(parents),rows=rows,witness=witness,resource_gate=gate,resource_samples=samples,source_sha256=hashlib.sha256(raw).hexdigest(),baseline_sha256=hashlib.sha256(baseline.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='All relative cube isometries for each completed pair consisting of the published51-vertex parent and a saved49-vertex parent. No coverage outside this saved bank is claimed.')
dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(status=status,seconds=out['seconds'],rows=[{k:r[k] for k in ['parent','permutations','minimum_intersection']} for r in rows],witness=witness and {k:witness[k] for k in ['parent','fixed_face_vertices']})),flush=True)
