"""Complete two-subpath placement optimum for one published Q7 parent."""
from pathlib import Path
import collections,hashlib,itertools,json,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
dest=H/'data/trim-census.json';assert not dest.exists()
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
source=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json';raw=source.read_bytes();p=json.loads(raw)['7']['vertices'];n=len(p);assert n==51
index={v:i for i,v in enumerate(p)};cap=10;hist=collections.Counter();eligible=0;permutations=0;intervals=0;best=0;witnesses=[];samples=[];status='COMPLETE';start=time.monotonic()
for perm in itertools.permutations(range(7)):
 images=[sum(((v>>k)&1)<<perm[k] for k in range(7)) for v in p];counts=[0]*128
 for u in p:
  for v in images:counts[u^v]+=1
 hist.update(counts);permutations+=1
 for t,count in enumerate(counts):
  if count>cap:continue
  eligible+=1;collisions=[(index[v^t],j) for j,v in enumerate(images) if v^t in index];assert len(collisions)==count
  for left in range(cap+1):
   for right in range(cap-left+1):
    intervals+=1;forbidden=[j for i,j in collisions if left<=i<n-right]
    cuts=[-1]+forbidden+[n]
    gap=max((b-a-1,a+1,b) for a,b in zip(cuts,cuts[1:]));length=n-left-right+gap[0]
    if length<2*n-cap:continue
    row=dict(permutation=list(perm),translation=t,intersection_count=count,collisions=collisions,first_interval=[left,n-right],second_interval=[gap[1],gap[2]],forest_vertices=length)
    if length>best:best=length;witnesses=[]
    if length==best and len(witnesses)<32:
     paths=[p[left:n-right],[128+(v^t) for v in images[gap[1]:gap[2]]]]
     assert sum(map(len,paths))==length and len(set(paths[0]+paths[1]))==length
     assert all((u^v).bit_count()!=1 for u in paths[0] for v in paths[1])
     for path in paths:assert all(((u^path[j]).bit_count()==1)==(j==i+1) for i,u in enumerate(path) for j in range(i+1,len(path)))
     row['paths']=paths;witnesses.append(row)
 if permutations%128==0:
  snap=snapshot();samples.append(snap)
  if snap['errors'] or snap['processes'] or snap['free_bytes']<768*1024**2:status='RESOURCE_LIMIT';break
if status=='COMPLETE':assert permutations==5040 and best>=2*n-cap and len(witnesses)>0
out=dict(status=status,seconds=time.monotonic()-start,permutations=permutations,isometries=128*permutations,intersection_histogram=dict(sorted(hist.items())),omission_cap=cap,eligible_isometries=eligible,first_intervals_examined=intervals,maximum_forest_vertices=best,witnesses=witnesses,resource_gate=gate,resource_samples=samples,source_sha256=hashlib.sha256(raw).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='All pairs of contiguous subpaths of the one published51-vertex Q7 snake, with arbitrary relative cube isometry. Each collision is a matching edge between parent positions, so deleting D positions removes at most D collisions. Maps with more than10 collisions or first-path trims exceeding10 cannot achieve92 vertices. For each remaining first interval the longest collision-free second interval is its largest gap. A saved witness of at least92 makes the finite cap sufficient for the global optimum within this construction family. Native census; no Lean replay of numerical entries.')
dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['status','seconds','isometries','eligible_isometries','first_intervals_examined','maximum_forest_vertices']}),flush=True)
