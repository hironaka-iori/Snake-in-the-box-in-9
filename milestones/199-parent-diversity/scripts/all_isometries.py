"""Exact translated-permutation intersection census for saved Q7 parents."""
from pathlib import Path
import argparse,collections,hashlib,itertools,json,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--parents');ap.add_argument('--seconds',type=float,default=90);ap.add_argument('--tag',required=True);a=ap.parse_args()
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
if a.parents:
 source=H/'data'/(a.parents+'.json');raw=source.read_bytes();parents=json.loads(raw)['parents']
else:
 source=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json';raw=source.read_bytes();parents=[dict(vertices=json.loads(raw)['7']['vertices'])]
start=time.monotonic();rows=[];witness=None;samples=[];status='COMPLETE'
for parent_id,parent in enumerate(parents):
 p=parent['vertices'];assert len(set(p))==len(p)
 hist=collections.Counter();best=128;examples=[];done=0
 for perm in itertools.permutations(range(7)):
  images=[sum(((v>>j)&1)<<perm[j] for j in range(7)) for v in p]
  counts=[0]*128
  for u in p:
   for v in images:counts[u^v]+=1
  # counts[t] is exactly |S intersect (perm(S) xor t)|.
  hist.update(counts);done+=1
  local=min(counts)
  if local<best:best=local;examples=[]
  if local==best and len(examples)<8:
   examples.extend(dict(permutation=list(perm),translation=t) for t,c in enumerate(counts) if c==best)
   examples=examples[:8]
  if local==0:
   t=counts.index(0);paths=[p,[128+(v^t) for v in images]]
   assert len(set(paths[0]+paths[1]))==2*len(p)
   assert all((u^v).bit_count()!=1 for u in paths[0] for v in paths[1])
   for q in paths:assert all(((u^q[j]).bit_count()==1)==(j==i+1) for i,u in enumerate(q) for j in range(i+1,len(q)))
   witness=dict(parent=parent_id,permutation=list(perm),translation=t,paths=paths,fixed_face_vertices=2*len(p));status='WITNESS';break
  if done%128==0:
   snap=snapshot();samples.append(snap)
   if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:status='RESOURCE_LIMIT';break
   if time.monotonic()-start>a.seconds:status='TIME_LIMIT';break
 rows.append(dict(parent=parent_id,permutations=done,isometries=128*done,minimum_intersection=best,minimum_examples=examples,intersection_histogram=dict(sorted(hist.items()))))
 if status!='COMPLETE':break
out=dict(status=status,seconds=time.monotonic()-start,arguments=vars(a),parents=len(parents),rows=rows,witness=witness,resource_gate=gate,resource_samples=samples,source_sha256=hashlib.sha256(raw).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='For each completed parent all 7! coordinate permutations and all 128 translations are evaluated exactly by the XOR difference counts. This covers 645120 cube isometries, beyond involutions. A resource/time stop leaves the remaining permutations or parents unresolved. No classification of all Q7 snakes is claimed.')
dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(status=status,seconds=out['seconds'],rows=[{k:r[k] for k in ['parent','permutations','minimum_intersection']} for r in rows],witness=witness and {k:witness[k] for k in ['parent','fixed_face_vertices']})),flush=True)
