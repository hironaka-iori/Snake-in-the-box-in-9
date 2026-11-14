"""All pointwise-compatible relative cube isometries across a single face cut."""
from pathlib import Path
import hashlib,itertools,json,math,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1]
source=H/'data/lower-dimensional-input.json';v=json.loads(source.read_bytes())['8']['vertices']
def canon(v):
    out=[]
    for w in [v,v[::-1]]:
        labels={};seq=[]
        for x,y in zip(w,w[1:]):
            a=(x^y).bit_length()-1
            if a not in labels:labels[a]=len(labels)
            seq.append(labels[a])
        out.append(tuple(seq))
    return min(out)
def valid(v):return len(v)==len(set(v)) and all(((x^v[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(v) for j in range(i+1,len(v)))
gate=snapshot();assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3
start=time.monotonic();records=[];examples=[]
for c in range(8):
    coords=[i for i in range(8) if i!=c];bit=1<<c
    A={x&~bit for x in v if not x&bit};B={x&~bit for x in v if x&bit};common=sorted(A&B);assert common
    anchor=common[0];classes={}
    for a in coords:classes.setdefault(tuple(((x^anchor)>>a)&1 for x in common),[]).append(a)
    cells=list(classes.values());total=math.prod(math.factorial(len(x)) for x in cells);accepted=0;different=0;maps=[]
    for images in itertools.product(*(itertools.permutations(cell) for cell in cells)):
        pi={a:b for cell,image in zip(cells,images) for a,b in zip(cell,image)}
        def h(x):return anchor^sum(((x^anchor)>>a&1)<<pi[a] for a in coords)
        assert all(h(x)==x for x in common)
        if any(h(x) in A for x in B if x not in A):continue
        accepted+=1;w=[x if not x&bit else bit|h(x&~bit) for x in v];assert valid(w)
        changed=canon(w)!=canon(v);different+=changed
        maps.append(dict(permutation=[pi[a] for a in coords],different_cube_class=changed,moved_indices=[i for i,(x,y) in enumerate(zip(v,w)) if x!=y]))
        if changed:examples.append(dict(coordinate=c,permutation=pi,anchor=anchor,original=v,vertices=w))
    r=dict(coordinate=c,crossing_projections=common,anchor=anchor,coordinate_cells=cells,candidates=total,accepted=accepted,different_images=different,maps=maps);records.append(r);print(c,'ports',len(common),'candidates',total,'accepted',accepted,'different',different,flush=True)
out=dict(status='COMPLETE',records=records,examples=examples,seconds=time.monotonic()-start,resource_gate=gate,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='All separate cube isometries on the two faces of every one-coordinate cut of the saved98-edgeQ8 path, normalized by a common global block isometry. Pointwise stabilizers of all crossing projections are completely enumerated. Native calculation only.')
(H/'data/face-isometries.json').write_text(json.dumps(out,indent=2)+'\n')
print('SAVED face-isometries.json',round(out['seconds'],3),'seconds')
