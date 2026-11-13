"""All conjugate matchings of the selected type on the published Q7 snake."""
from pathlib import Path
import collections,hashlib,itertools,json,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
source=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json';raw=source.read_bytes();seeds=json.loads(raw);p=seeds['7']['vertices']
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
assert len(p)==51 and len(set(p))==51
assert all((((v^p[j]).bit_count()==1)==(j==i+1)) for i,v in enumerate(p) for j in range(i+1,len(p)))
start=time.monotonic();rows=[];best=0;witnesses=[];keys=set();hist=collections.Counter()
for fixedflip in range(7):
 for moved in itertools.combinations([k for k in range(7) if k!=fixedflip],4):
  a,b,c,d=moved
  for pairs in [[(a,b),(c,d)],[(a,c),(b,d)],[(a,d),(b,c)]]:
   perm=list(range(7))
   for u,v in pairs:perm[u],perm[v]=v,u
   for mask in range(4):
    shift=1<<fixedflip
    for k,(u,v) in enumerate(pairs):
     if (mask>>k)&1:shift^=(1<<u)|(1<<v)
    def h(v):return sum(((v>>i)&1)<<perm[i] for i in range(7))^shift
    key=tuple(perm),shift;assert key not in keys;keys.add(key)
    assert all(h(h(v))==v and h(v)!=v for v in range(128))
    index={v:i for i,v in enumerate(p)}
    conflicts=[(i,index[h(v)]) for i,v in enumerate(p) if h(v) in index and i<index[h(v)]]
    hist[len(conflicts)]+=1;left=0;local=0;windows=[];last={}
    for right,v in enumerate(p):
     orbit=min(v,h(v))
     if orbit in last:left=max(left,last[orbit]+1)
     last[orbit]=right
     length=right-left+1
     if length>local:local=length;windows=[]
     if length==local:windows.append([left,right])
    row=dict(permutation=perm[:],translation=shift,fixed_flip=fixedflip,pairs=pairs,
      full_path_conflicts=conflicts,maximum_subpath_vertices=local,maximal_windows=windows)
    rows.append(row)
    if local>best:best=local;witnesses=[]
    if local==best:
     for l,r in windows:
      first=p[l:r+1];second=[h(v)+128 for v in first]
      assert len(set(first+second))==2*local and all((u^v).bit_count()!=1 for u in first for v in second)
      for path in [first,second]:assert all((((v^path[j]).bit_count()==1)==(j==i+1)) for i,v in enumerate(path) for j in range(i+1,len(path)))
      witnesses.append(dict(matching=len(rows)-1,start=l,end=r,paths=[first,second],forest_vertices=2*local))
assert len(rows)==1260
out=dict(status='COMPLETE',seconds=time.monotonic()-start,resource_gate=gate,source_sha256=hashlib.sha256(raw).hexdigest(),
 script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),matchings=len(rows),maximum_subpath_edges=best-1,maximum_forest_vertices=2*best,
 full_path_conflict_histogram=dict(hist),rows=rows,witnesses=witnesses,
 scope='All1260 affine involutions on Q7 with two coordinate transpositions, exactly one flipped fixed coordinate, and either00 or11 translation on each swapped pair. All contiguous subpaths of the specified50-edge Q7 snake. This does not classify all Q7 snakes or allow use of the extra quotient matching edges as path steps.')
dest=H/'data/placements.json';assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','seconds','matchings','maximum_subpath_edges','maximum_forest_vertices','full_path_conflict_histogram']}))
