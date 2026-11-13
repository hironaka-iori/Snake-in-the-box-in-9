from pathlib import Path
import argparse,hashlib,json,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--keep',type=int,default=24);ap.add_argument('--target',type=int,default=50);ap.add_argument('--limit',type=int,default=256);ap.add_argument('--nodes',type=int,default=3000000);ap.add_argument('--seconds',type=float,default=30);ap.add_argument('--tag',required=True);a=ap.parse_args()
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json';raw=source.read_bytes();base=json.loads(raw)['7']['vertices']
N=[sum(1<<(v^(1<<k)) for k in range(7)) for v in range(128)]
def canonical(path):
 steps=[(u^v).bit_length()-1 for u,v in zip(path,path[1:])]
 def normal(ts):
  labels={};out=[]
  for t in ts:
   if t not in labels:labels[t]=len(labels)
   out.append(labels[t])
  return tuple(out)
 return min(normal(steps),normal(steps[::-1]))
seen=set();parents=[];rows=[]
for orient,seed in enumerate([base,base[::-1]]):
 prefix=seed[:a.keep];path=prefix[:];blocked=sum(1<<v for v in prefix)
 for v in prefix[:-1]:blocked|=N[v]
 start=time.monotonic();nodes=0;stop=None;leaves=0;samples=[]
 def visit(blocked):
  global nodes,stop,leaves
  nodes+=1
  if len(path)==a.target:
   leaves+=1;key=canonical(path)
   if key not in seen:
    assert len(set(path))==len(path) and all(((v^path[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(path) for j in range(i+1,len(path)))
    seen.add(key);parents.append(dict(vertices=path[:],canonical=list(key),orientation=orient))
    if len(parents)>=a.limit:stop='CLASS_LIMIT'
   return
  if nodes>a.nodes:stop='NODE_LIMIT';return
  if nodes%2048==0:
   if time.monotonic()-start>a.seconds:stop='TIME_LIMIT';return
   snap=snapshot();samples.append(snap)
   if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:stop='RESOURCE_LIMIT';return
  available=N[path[-1]]&~blocked;newblocked=blocked|N[path[-1]];choices=[]
  while available:
   bit=available&-available;v=bit.bit_length()-1;available-=bit
   choices.append(((N[v]&~newblocked).bit_count(),v))
  for _,v in sorted(choices):
   path.append(v);visit(newblocked|(1<<v));path.pop()
   if stop:return
 visit(blocked)
 rows.append(dict(orientation=orient,prefix=prefix,status=stop or 'EXHAUSTED',nodes=nodes,leaves=leaves,seconds=time.monotonic()-start,resource_samples=samples))
 if stop in ['RESOURCE_LIMIT','CLASS_LIMIT']:break
out=dict(arguments=vars(a),parents=parents,rows=rows,resource_gate=gate,source_sha256=hashlib.sha256(raw).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Ordered Q7 extensions of the specified published-seed prefixes to the target vertex count. Distinct transition words normalized under coordinate relabelling and reversal; translation is removed by using transitions. Resource/node/class/time caps are not exhaustion.')
dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(classes=len(parents),rows=[{k:r[k] for k in ['status','nodes','leaves','seconds']} for r in rows])),flush=True)
