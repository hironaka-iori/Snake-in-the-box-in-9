import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)
from collections import Counter
A=[0,1,2,5,6,13,24,26,27,28,29]; B=[3,4,7,8,9,11,12,16,20,23,31]
M=[x for x in range(32) if x not in A and x not in B]
def pieces(allowed, h=5):
    al=0
    for x in allowed: al|=1<<x
    nbm=[sum(1<<(x^(1<<d)) for d in range(h)) for x in range(1<<h)]
    out=[]
    def rec(path, used, blocked):
        out.append(tuple(path))
        cur=path[-1]
        for d in range(h):
            y=cur^(1<<d)
            if not (al>>y)&1 or (blocked>>y)&1: continue
            if nbm[y] & used & ~(1<<cur): continue
            path.append(y); rec(path, used|(1<<y), blocked|nbm[cur]|(1<<y)); path.pop()
    for s in allowed: rec([s],1<<s,1<<s)
    return out
if __name__=='__main__':
    P=pieces(A+M)
    Ms=set(M)
    c=Counter(len(p) for p in P); print('all',sorted(c.items()))
    PM=[p for p in P if p[0] in Ms and p[-1] in Ms]
    c=Counter(len(p) for p in PM); print('M-to-M',sorted(c.items()), len(PM))
    print('max spine use in an M-to-M piece', max(sum(1 for x in p if x in set(A)) for p in PM))
    best=[p for p in PM if len(p)>=14]; print(best[:4])
