from pathlib import Path
import sys
from collections import Counter
root=Path(__file__).resolve().parent
n=int(sys.argv[1])
def signature(p):
    # Pair differences remove translations; sorting coordinate incidence columns removes relabelings.
    def oriented(anchors):
        columns=[0]*9
        for u,v in zip(anchors,anchors[1:]):
            mask=u^v
            assert mask.bit_count()==2
            for d in range(9):columns[d]=2*columns[d]+((mask>>d)&1)
        return tuple(sorted(columns))
    return min(oriented(p),oriented(p[::-1]))
def verify(p):
    return len(set(p))==len(p) and all(0<=v<512 for v in p) and all(((x^y).bit_count()==1)==(i==j+1) for i,x in enumerate(p) for j,y in enumerate(p[:i]))
seen=set()
for w in (root/'all_near_registered.words').read_text().split():
    p=[0]
    for c in w:p.append(p[-1]^(1<<int(c)))
    for i in range(len(p)-n):
        anchors=p[i:i+n+1:2]
        if all((x^y).bit_count()==2 for x,y in zip(anchors,anchors[1:])):seen.add(signature(anchors))
hist=Counter();arch=len(seen)
with (root/f'new_order_{n}.pts').open('w') as out:
    for line in (root/f'cross_seeds_{n}.txt').read_text().splitlines():
        kind,score,*xs=line.split();p=list(map(int,xs))
        if kind=='FOUND':
            assert len(p)-1==int(score) and verify(p)
            print('FOUND',p);break
        assert len(p)==n+1 and all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
        a=p[::2];assert len(a)==len(set(a))
        k=signature(a)
        if k in seen:continue
        seen.add(k);hist[int(score)]+=1
        print(*p,file=out)
print('target',n,'archive anchor patterns',arch,'different anchor patterns',dict(sorted(hist.items())))
