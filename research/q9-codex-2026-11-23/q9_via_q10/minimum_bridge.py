"""For each surviving rigid placement, price all monotone bridges by number of chords."""
from collections import Counter,deque
from pathlib import Path
import json
import random
root=Path(__file__).resolve().parent
rng=random.Random(834547)
def vertices(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<(ord(c)-65))
    return p
def word(p):
    assert all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
    return ''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]))
def canon(w):
    table={}
    return ''.join(table.setdefault(c,str(len(table))) for c in w)
def shape(w):return min(canon(w),canon(w[::-1]))
arms=[vertices(w) for w in (root/'q8_95.words').read_text().split()]
near={}; connected=0; dist_hist=Counter(); rows=0;combinations=0;minimum=Counter();placements=set()
for line in (root/'revisit_two95.pts').read_text().splitlines():
    s=line.split()
    if not s:continue
    if s[0]=='COUNT': rows+=1;continue
    assert s[0]=='PLACE'
    idx=int(s[1]);left=arms[idx];right=list(map(int,s[2:]))
    assert (idx,tuple(right)) not in placements;placements.add((idx,tuple(right)))
    assert len(right)==96==len(set(right)) and all(0<=v<512 for v in right) and len(word(right))==95
    assert all((x^y).bit_count()>=2 for x in left for y in right)
    blocked=set()
    for x in left[1:]+right[1:]:
        blocked.add(x);blocked.update(x^(1<<i) for i in range(9))
    avail=set(range(512))-blocked|{left[0],right[0]}
    q=deque([left[0]]);visited={left[0]}
    while q:
        x=q.popleft()
        for i in range(9):
            v=x^1<<i
            if v in avail and v not in visited:visited.add(v);q.append(v)
    connected+=right[0] in visited
    used=set(left+right)
    halo={v:sum((x^v).bit_count()==1 for x in used) for v in range(512) if v not in used}
    for a in (left,left[::-1]):
        for b in (right,right[::-1]):
            start=a[0];end=b[0];mask=start^end;d=mask.bit_count();dist_hist[d]+=1;combinations+=1
            cost={0:0};parent={}
            for n in range(1,mask+1):
                if n&~mask:continue
                v=n^start
                if v in used and n!=mask:continue
                choices=[(cost[n^bit],n^bit) for i in range(9) if (bit:=1<<i)&n and n^bit in cost]
                if not choices:continue
                best=min(c for c,_ in choices);parent[n]=[prev for c,prev in choices if c==best]
                cost[n]=best+(0 if n==mask else halo[v]-(n.bit_count()==1)-((n^mask).bit_count()==1))
            if mask not in cost:continue
            minimum[cost[mask]]+=1
            for _ in range(8):
                bridge=[];x=mask
                while x:bridge.append(start^x);x=rng.choice(parent[x])
                p=a[::-1]+bridge[::-1]+b[1:]
                key=shape(word(p))
                if key in near:continue
                assert len(p)==len(set(p))==191+d
                chords=sum((x^y).bit_count()==1 for j,y in enumerate(p) for x in p[:max(j-1,0)])
                assert chords==cost[mask]
                near[key]=chords
(root/'monotone_near.words').write_text('\n'.join(sorted(near))+'\n')
stats=dict(left_rows=rows,placements=len(placements),connected_original_tips=connected,endpoint_pairs=combinations,hamming_distance=dict(sorted(dist_hist.items())),minimum_chords=dict(sorted(minimum.items())),distinct_near_walks=len(near),near_by_length=dict(sorted(Counter(map(len,near)).items())),near_by_chords=dict(sorted(Counter(near.values()).items())))
(root/'minimum_bridge.json').write_text(json.dumps(stats,indent=2)+'\n')
print(stats)
