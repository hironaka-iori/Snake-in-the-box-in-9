"""Validate and canonicalize pairs of mutually nonadjacent induced Q8 paths."""
import json,sys
from pathlib import Path
from collections import Counter
def decode(line):
    xs=list(map(int,line.split()));n=xs[0];a=tuple(xs[1:1+n]);m=xs[n+1];b=tuple(xs[n+2:])
    assert len(a)==n and len(b)==m and n>0 and m>0 and all(0<=x<256 for x in a+b)
    for path in (a,b):
        assert len(set(path))==len(path) and all(((u^path[j]).bit_count()==1)==(j==i+1) for i,u in enumerate(path) for j in range(i+1,len(path)))
    assert all((u^v).bit_count()>=2 for u in a for v in b)
    return a,b
def canonical(a,b):
    forms=[]
    for l,r in [(a,b),(b,a)]:
        for p in (l,l[::-1]):
            for q in (r,r[::-1]):
                walk=[x^p[0] for x in p+q]
                sig=[sum(((v>>d)&1)<<j for j,v in enumerate(walk)) for d in range(8)]
                order=sorted(range(8),key=sig.__getitem__);mp=[0]*256
                for i,d in enumerate(order):
                    for j in range(256):
                        if j>>d&1:mp[j]|=1<<i
                t=tuple(mp[x] for x in walk);forms.append((len(p),*t[:len(p)],len(q),*t[len(p):]))
    return min(forms)
def main():
    out=sys.argv[1];seen=set();raw=set();sizes=Counter()
    for file in sys.argv[2:]:
        for l in open(file):
            if not l.strip() or l in raw:continue
            raw.add(l);a,b=decode(l);key=canonical(a,b)
            if key not in seen:seen.add(key);sizes[len(a)+len(b)]+=1
    with open(out,'w') as f:
        for row in sorted(seen):print(*row,file=f)
    print('distinct',len(seen),'vertex_counts',dict(sizes))
if __name__=='__main__':main()

