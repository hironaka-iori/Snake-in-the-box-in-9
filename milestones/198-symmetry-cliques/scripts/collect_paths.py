from pathlib import Path
import argparse,hashlib,json,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--keep',type=int,default=38);ap.add_argument('--target',type=int,default=50);ap.add_argument('--seconds',type=float,default=40);ap.add_argument('--nodes',type=int,default=1000000);ap.add_argument('--tag',required=True);a=ap.parse_args()
dest=H/'data'/(a.tag+'.json');assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=H/'data/structure.json';raw=source.read_bytes();d=json.loads(raw);case=d['case']
def h(v):return sum(((v>>i)&1)<<case['permutation'][i] for i in range(7))^case['translation']
def g(v):return h(v&127)|((1-((v>>7)&1))<<7)
def orb(v):return min(v,g(v))
N=[sum(1<<w for w in set([v^(1<<k) for k in range(7)]+[h(v)])) for v in range(128)]
base=d['seed'][5:51];rows=[];witness=None
for orientation in [base,base[::-1]]:
 prefix=orientation[:a.keep];path=prefix[:];blocked=sum(1<<v for v in prefix)
 for v in prefix[:-1]:blocked|=N[v]
 nodes=0;start=time.monotonic();stop=None;samples=[];best=prefix[:];bank=[];bank_count=0
 def visit(blocked):
  global nodes,stop,best,bank,bank_count
  nodes+=1
  if len(path)>len(best):best=path[:];bank=[];bank_count=0
  if len(path)==len(best):
   bank_count+=1
   if len(bank)<2048:bank.append(path[:])
  if len(path)==a.target:return path[:]
  if nodes>a.nodes:stop='NODE_LIMIT';return None
  if nodes%4096==0:
   if time.monotonic()-start>a.seconds:stop='TIME_LIMIT';return None
   snap=snapshot();samples.append(snap)
   if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:stop='RESOURCE_LIMIT';return None
  available=N[path[-1]]&~blocked
  if not available:return None
  candidates=[]
  while available:
   bit=available&-available;v=bit.bit_length()-1;available-=bit
   candidates.append(((N[v]&~(blocked|N[path[-1]])).bit_count(),v))
  newblocked=blocked|N[path[-1]]
  for _,v in sorted(candidates):
   path.append(v);found=visit(newblocked|(1<<v));path.pop()
   if found:return found
   if stop:return None
  return None
 found=visit(blocked)
 assert all(bool(N[v]&(1<<best[j]))==(j==i+1) for i,v in enumerate(best) for j in range(i+1,len(best)))
 rows.append(dict(status='WITNESS' if found else stop or 'EXHAUSTED',nodes=nodes,seconds=time.monotonic()-start,prefix=prefix,best=best,bank=bank,bank_count=bank_count,resource_samples=samples))
 if found:
  lift=[found[0]]
  for z in found[1:]:
   opts=[lift[-1]^(1<<k) for k in range(8) if orb(lift[-1]^(1<<k))==z];assert len(opts)==1;lift.append(opts[0])
  partner=[g(v) for v in lift]
  assert len(set(lift+partner))==2*len(lift) and all((v^w).bit_count()!=1 for v in lift for w in partner)
  for p in [lift,partner]:assert all(((v^p[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(p) for j in range(i+1,len(p)))
  witness=dict(quotient_path=found,paths=[lift,partner],fixed_face_vertices=2*len(lift));break
 if stop=='RESOURCE_LIMIT':break
out=dict(arguments=vars(a),rows=rows,witness=witness,resource_gate=gate,source_sha256=hashlib.sha256(raw).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='All legal ordered extensions of each displayed prefix in the row4147 quotient until the explicit node/time/resource limit. EXHAUSTED excludes only that fixed prefix. Prefixes are taken in both orientations of the saved46-vertex direct path.')
dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(witness=bool(witness),rows=[{k:r[k] for k in ['status','nodes','seconds']}|dict(best_vertices=len(r['best'])) for r in rows])),flush=True)
