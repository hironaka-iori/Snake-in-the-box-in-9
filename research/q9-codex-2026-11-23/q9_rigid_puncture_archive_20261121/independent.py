from itertools import permutations
from collections import defaultdict, Counter
from pathlib import Path
import json

out = Path(__file__).resolve().parent
root = out.parent
def steps(word):
    p=[0]
    for x in word:
        p.append(p[-1] ^ (1 << x))
    return p

def read(file):
    return [list(map(int,s)) for s in file.read_text().split()]

def signature(w):
    mask=[0]*9
    for j,d in enumerate(w):
        mask[d] |= 1 << j
    return tuple(mask)

def is_path(p):
    return len(set(p))==len(p) and all(((a^b).bit_count()==1)==(j==i+1) for i,a in enumerate(p) for j,b in enumerate(p[i+1:],i+1))

def axes_for(source,target):
    missing_source=[j for j in range(8) if source[j]==0]
    missing_target=[j for j in range(9) if target[j]==0]
    amap=[target.index(t) if t else -1 for t in source[:8]]
    for perm in permutations(missing_target,len(missing_source)):
        for j,d in zip(missing_source,perm):
            amap[j]=d
        yield tuple(amap)

def images(p, amap):
    v=[0]*256
    for j in range(8):
        for x in range(1<<j):
            v[x+(1<<j)]=v[x] | (1<<amap[j])
    return [v[x] for x in p]

bank=read(root/'q8_catalogue_96_98.words')
archive=read(root/'q9_gap_generations/prior191.words')
paths=list(map(steps,archive)); sets=list(map(set,paths))
assert all(len(p)==192 and is_path(p) for p in paths)
def norm(w):
    rev={}
    return tuple(rev.setdefault(i,len(rev)) for i in w)
assert len({min(norm(w),norm(w[::-1])) for w in archive})==131
index=defaultdict(list)
for r,w in enumerate(archive):
    for k in range(len(w)-46):
        sig=signature(w[k:k+47])
        index[tuple(sorted(sig))].append((r,k,sig))
counts=Counter(); found=set()
for i,w in enumerate(bank):
    p=steps(w)
    inner=set(p[1:-1])
    if any(all((v ^ 1<<j) not in inner for j in range(8)) for v in set(range(256))-set(p)):
        continue
    counts['rigid']+=1
    assert len(p)==97 and is_path(p)
    cache={}
    for h in range(97):
        a,b=(0,h-1) if h>=96-h else (h+1,96)
        s=a+(b-a-47)//2
        w47=w[s:s+47]
        for start,oriented in ((s,w47),(s+47,w47[::-1])):
            sig=signature(oriented)
            for r,k,tgt in index[tuple(sorted(sig))]:
                counts['fixed_47_anchor_matches']+=1
                for amap in axes_for(sig,tgt):
                    counts['complete_maps']+=1
                    if amap not in cache:
                        cache[amap]=images(p,amap)
                    moved=cache[amap]; off=paths[r][k]^moved[start]
                    if (off^moved[h]) in sets[r]:
                        continue
                    if all((off^x) in sets[r] for j,x in enumerate(moved) if j!=h):
                        found.add((i,h,r,off,amap))
hits=[json.loads(s) for s in (out/'hits.jsonl').read_text().splitlines()]
assert found=={(z['donor'],z['hole'],z['archive'],z['translation'],tuple(z['axes'])) for z in hits}
def place(x,m):
    return sum(1<<a for j,a in enumerate(m) if (x>>j)&1)
for z in hits:
    verts=z['vertices']; p=steps(bank[z['donor']]); h=z['hole']; m=z['axes']; m=m+list(set(range(9))-set(m))
    assert len(verts)==192 and is_path(verts)
    assert paths[z['archive']]==[z['translation']^place(x,m) for x in verts]
    assert set(p)-set(verts)=={p[h]} and p[h]==z['vertex']
    assert z['missing_opposite_occupied']==((p[h]+256) in verts)
    assert z['layer_population']==sum(v<256 for v in verts)
    assert z['layer_visits']==1+sum((v^w)==256 for v,w in zip(verts,verts[1:]))
strict=sorted([z for z in hits if 0<z['hole']<96 and z['layer_population']==96],key=lambda z:z['donor'])
groups=defaultdict(list)
for z in hits:
    groups[z['donor'],z['hole']].append(z)
reps=[min(zs,key=lambda z:(z['layer_population'],z['missing_opposite_occupied'],z['archive'])) for k,zs in sorted(groups.items())]
for name,rows in [('strict_interior_191.jsonl',strict),('one_per_hole.jsonl',reps)]:
    (out/name).write_text(''.join(json.dumps(z,separators=(',',':'))+'\n' for z in rows))
print(json.dumps(dict(counts=counts,embeddings=len(found),distinct_donor_holes=len(reps),matches_primary=True,archive_classes=len(paths),checked_pairs_per_witness=192*191//2,strict_interior=[{k:z[k] for k in ('donor','hole','vertex','archive','missing_opposite_occupied','layer_visits')} for z in strict],lower_counts=Counter(z['layer_population'] for z in hits),crossings=Counter(z['layer_visits']-1 for z in hits),internal_count=sum(0<z['hole']<96 for z in hits),opposite_occupied=sum(z['missing_opposite_occupied'] for z in hits)),indent=2))
