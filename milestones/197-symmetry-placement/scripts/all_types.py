"""Classify all affine involution matchings on Q7 and place the fixed path."""
from pathlib import Path
import collections,hashlib,itertools,json,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
source=R/'milestones/188-dimensional-constructions/data/lower-dimensional-seeds.json';raw=source.read_bytes();p=json.loads(raw)['7']['vertices']
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
def pairings(xs):
 if not xs:yield [];return
 first=xs[0]
 for j in range(1,len(xs)):
  for rest in pairings(xs[1:j]+xs[j+1:]):yield [(first,xs[j])]+rest
start=time.monotonic();rows=[];summaries=[];best=0;witnesses=[];keys=set()
for r in range(4):
 for f in range(8-2*r):
  records=[];bestlocal=0;minimum=100;hist=collections.Counter()
  for moved in itertools.combinations(range(7),2*r):
   remaining=[i for i in range(7) if i not in moved]
   for pairs in pairings(list(moved)):
    perm=list(range(7))
    for a,b in pairs:perm[a],perm[b]=b,a
    for flips in itertools.combinations(remaining,f):
     for mask in range(1<<r):
      shift=sum(1<<i for i in flips)
      for j,(a,b) in enumerate(pairs):
       if (mask>>j)&1:shift^=(1<<a)|(1<<b)
      def h(v):return sum(((v>>i)&1)<<perm[i] for i in range(7))^shift
      key=tuple(perm),shift;assert key not in keys;keys.add(key)
      assert all(h(h(v))==v for v in range(128))
      index={v:i for i,v in enumerate(p)};conflicts=[(i,index[h(v)]) for i,v in enumerate(p) if h(v) in index and i<=index[h(v)]]
      hist[len(conflicts)]+=1;minimum=min(minimum,len(conflicts));left=0;local=0;windows=[];last={}
      for right,v in enumerate(p):
       if h(v)==v:left=right+1;continue
       orbit=min(v,h(v))
       if orbit in last:left=max(left,last[orbit]+1)
       last[orbit]=right;length=right-left+1
       if length>local:local=length;windows=[]
       if length==local:windows.append([left,right])
      record=dict(transpositions=r,flipped_fixed=f,permutation=perm[:],translation=shift,pairs=pairs,fixed_flips=flips,
       full_path_conflicts=conflicts,maximum_subpath_vertices=local,maximal_windows=windows)
      records.append(len(rows));rows.append(record);bestlocal=max(bestlocal,local)
      if local>best:best=local;witnesses=[]
      if local and local==best:
       for l,u in windows:
        first=p[l:u+1];second=[h(v)+128 for v in first]
        assert len(set(first+second))==2*local and all((v^w).bit_count()!=1 for v in first for w in second)
        witnesses.append(dict(matching=len(rows)-1,start=l,end=u,paths=[first,second],forest_vertices=2*local))
  summaries.append(dict(transpositions=r,flipped_fixed=f,matching_count=len(records),minimum_full_path_conflicts=minimum,maximum_subpath_edges=bestlocal-1,conflict_histogram=dict(hist)))
assert len(rows)==6512 and len(summaries)==20
out=dict(status='COMPLETE',seconds=time.monotonic()-start,resource_gate=gate,source_sha256=hashlib.sha256(raw).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 matchings=len(rows),types=summaries,rows=rows,maximum_subpath_edges=best-1,maximum_forest_vertices=2*best,witnesses=witnesses,
 scope='All affine cube involutions h on Q7, including fixed points. Extend to the free Q8 involution g(y,b)=(h(y),1-b). All contiguous subpaths of the displayed50-edge Q7 path avoiding h contacts, including fixed vertices. The restricted paths do not use extra matching edges.')
dest=H/'data/placements-all.json';assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(status='COMPLETE',seconds=out['seconds'],maximum_subpath_edges=best-1,maximum_forest_vertices=2*best,types=summaries)))
