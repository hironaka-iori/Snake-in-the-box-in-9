"""Check every printed record using its actual nine-bit path."""
import sys
from pathlib import Path
def mirror(x,t):
    for i in range(0,2*t,2):
        if (x>>i ^ x>>(i+1)) & 1:x ^= 3<<i
    return x
for k in range(1,len(sys.argv),2):
    t=int(sys.argv[k]);fn=Path(sys.argv[k+1]);count=0;best=-1
    for line in fn.read_text().splitlines():
        ws=line.split();declared=int(ws[1]);w1,mid,w2=map(int,ws[5:8]);p=list(map(int,ws[9:]))
        assert 2*(w1+mid+w2)==declared==len(p)-1
        assert set(p)<=set(range(512)) and len(p)==len(set(p))
        assert all((x^y).bit_count()==(1) for x,y in zip(p,p[1:]))
        assert all((x^y).bit_count()>1 for j,x in enumerate(p) for y in p[j+2:])
        assert p[declared//2]==0 and all(mirror(x,t)==y for x,y in zip(p,reversed(p)))
        h=p[declared//2+1:]
        assert all(v%4==0 for v in h[:w1])
        assert all(v%4 in (1,2) for v in h[w1:w1+mid])
        assert all(v%4==3 for v in h[w1+mid:])
        best=max(best,declared);count+=1
    print(fn.name,'verified',count,'largest',best)
