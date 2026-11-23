import json
from pathlib import Path
def shapes(p):
    return tuple(sorted(p[1::2]))
sets={}
for i,l in enumerate(Path("q9_onechord_expanded_800.txt").read_text().splitlines()):
    p=list(map(int,l.split()))
    assert len(set(p))==193 and len(p)==193 and all(0<=v<512 for v in p)
    assert all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
    assert sum((x^p[j]).bit_count()==1 for k,x in enumerate(p) for j in range(k+2,len(p)))==1
    sets.setdefault(shapes(p),[]).append(i)
for s in sets: print(*s)
