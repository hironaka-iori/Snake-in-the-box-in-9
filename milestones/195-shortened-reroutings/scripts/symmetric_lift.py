"""Extract the observed involution and enumerate two-face joins of its path.

The finite family consists of two contiguous subpaths of the observed
25-edge quotient path, one transformed by a specified commuting cube isometry.
It is not an optimization over all quotient paths.
"""
from pathlib import Path
import hashlib,itertools,json,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
source=H/'data/forest-profiles.json';raw=source.read_bytes();d=json.loads(raw)
p,q=d['comparisons']['8']['blocks'][1::2]
def g(v):return (v^(((v>>2)^(v>>5))&1)*((1<<2)|(1<<5)))^73
def orbit(v):return min(v,g(v))
assert all(g(g(v))==v and (v^g(v)).bit_count()>=3 for v in range(128))
assert [g(v) for v in p]==q
base=sorted({orbit(v) for v in range(128)})
N={v:{orbit(v^(1<<k)) for k in range(7)} for v in base}
P=[orbit(v) for v in p]
assert len(set(P))==26 and all(((P[j] in N[u])==(j==i+1)) for i,u in enumerate(P) for j in range(i+1,len(P)))
start=time.monotonic();best=-1;witness=None;maps=0;hist={}
def transform(v,perm,shift):return sum(((v>>i)&1)<<perm[i] for i in range(7))^shift
for flipperm in itertools.permutations([0,3,6]):
 for unflipperm in itertools.permutations([1,4]):
  for swapped in [False,True]:
   perm=list(range(7))
   for i,j in zip([0,3,6],flipperm):perm[i]=j
   for i,j in zip([1,4],unflipperm):perm[i]=j
   if swapped:perm[2],perm[5]=5,2
   for shift in range(128):
    if ((shift>>2)&1)!=((shift>>5)&1):continue
    maps+=1;T=[orbit(transform(v,perm,shift)) for v in p]
    # Each direction gives the path portion ending at the crossing port and
    # the other portion beginning there. Extend until the first extra overlap.
    index={v:j for j,v in enumerate(T)}
    for i,v in enumerate(P):
     if v not in index:continue
     j=index[v]
     for signP in [-1,1]:
      armP=[];a=i
      while 0<=a<len(P):armP.append(P[a]);a+=signP
      for signT in [-1,1]:
       armT=[];b=j
       while 0<=b<len(T):armT.append(T[b]);b+=signT
       positions={v:k for k,v in enumerate(armT)};limit=len(armT)
       for used,v in enumerate(armP,1):
        if used>1 and v in positions:limit=min(limit,positions[v])
        total=used+limit-1 # two edge counts plus one crossing
        if total>best:
         best=total;witness=dict(permutation=perm[:],translation=shift,port=v if used==1 else armP[0],
             first=list(reversed(armP[:used])),second=armT[:limit],first_direction=signP,second_direction=signT)
    overlap=len(set(P)&set(T));hist[overlap]=hist.get(overlap,0)+1
assert maps==1536
# Lift the quotient path to Q8, choosing the unique actual neighbour at each step.
quotient_path=witness['first']+[v+128 for v in witness['second']]
lift=[quotient_path[0]]
def orbit8(v):return orbit(v&127)+(v&128)
for z in quotient_path[1:]:
    candidates=[lift[-1]^(1<<k) for k in range(8) if orbit8(lift[-1]^(1<<k))==z]
    assert len(candidates)==1;lift.append(candidates[0])
partner=[g(v&127)+(v&128) for v in lift]
assert len(lift)-1==best and len(set(lift+partner))==2*len(lift)
assert all((u^v).bit_count()!=1 for u in lift for v in partner)
for path in [lift,partner]:
 assert all((((u^path[j]).bit_count()==1)==(j==i+1)) for i,u in enumerate(path) for j in range(i+1,len(path)))
out=dict(status='COMPLETE',source_sha256=hashlib.sha256(raw).hexdigest(),seconds=time.monotonic()-start,
    observed_symmetry=dict(permutation=[0,1,5,3,4,2,6],translation=73,minimum_partner_distance=3),
    quotient_vertices=len(base),quotient_degree=sorted({len(ns) for ns in N.values()}),
    commuting_isometries=maps,full_path_overlap_histogram=hist,maximum_joined_edges=best,
    witness=witness,quotient_path=quotient_path,paths=[lift,partner],fixed_face_vertices=2*len(lift),
    scope='All two-subpath, one-crossing joins of the observed25-edge quotient path under1536 specified commuting isometries. Native enumeration and independent full-path validation. No unrestricted quotient optimum.')
target=H/'data/symmetric-lift.json';assert not target.exists();target.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','seconds','commuting_isometries','maximum_joined_edges','fixed_face_vertices','full_path_overlap_histogram']}))
