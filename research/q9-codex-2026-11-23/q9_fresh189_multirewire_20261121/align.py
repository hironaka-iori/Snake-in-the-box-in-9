from pathlib import Path
from collections import defaultdict
from functools import lru_cache
import random,itertools,json
D=Path(__file__).resolve().parent
words=(D.parent/'q9_uncovered_abab_20261121/outside_wordbanks189.words').read_text().split()
def path(w):
    p=[0]
    for d in w:p.append(p[-1]^1<<int(d))
    return p
def sig(w):return bytes(w.index(d) for d in w)
@lru_cache(4096)
def table(m):
    q=[0]*512
    for x in range(1,512):
        l=x&-x;q[x]=q[x^l]^(1<<m[l.bit_length()-1])
    return q
def poses():
    rng=random.Random(868153)
    for i,j in itertools.combinations(range(16),2):
        a,b=words[i],words[j];A=path(a);B=path(b);aset=set(A);opts=defaultdict(list);width=10
        for k in range(len(b)-width+1):
            u=b[k:k+width];opts[sig(u)].append((k,u));opts[sig(u[::-1])].append((k+width,u[::-1]))
        pairs=[(k,v,u) for k in range(len(a)-width+1) for v,u in opts[sig(a[k:k+width])]]
        rng.shuffle(pairs);bank={}
        for k,v,u in pairs[:420]:
            h=dict(zip(map(int,u),map(int,a[k:k+width])));left=sorted(set(range(9))-set(h));right=sorted(set(range(9))-set(h.values()));rng.shuffle(right);h.update(zip(left,right));m=tuple(h[z] for z in range(9));T=table(m);x=A[k]^T[B[v]]
            if (m,x) in bank:continue
            q=[x^T[t] for t in B];overlap=len(aset&set(q))
            if 65<=overlap<190:bank[(m,x)]=(overlap,q)
        groups=[[z for z in bank if lo<=bank[z][0]<=hi] for lo,hi in [(65,109),(110,144),(145,169),(170,189)]]
        for group in groups:
            rng.shuffle(group)
            for m,x in group[:4]:
                cm,q=bank[m,x];yield [i,j,''.join(map(str,m)),x,cm],A,q
if __name__=='__main__':
    with (D/'poses.dat').open('w') as f,(D/'poses.meta').open('w') as g:
        for tag,a,b in poses():print(*a,*b,file=f);print(*tag,file=g)
