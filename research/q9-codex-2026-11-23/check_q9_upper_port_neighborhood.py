import gzip,itertools,random,collections
from pathlib import Path
def stats(P):
    counts=collections.Counter(x^(1<<d) for x in P for d in range(8))
    available_incidence=sum(r for r in counts.values() if r<=2)
    return len(counts),available_incidence,sum((x^y).bit_count()==2 for x,y in itertools.combinations(P,2))
def drop(x,i):return (x%(1<<i))|((x>>(i+1))<<i)
def bound(m,k):return 255-m+3*k
def pairmin(m,k):return max(0,(5*k-255+m+1)//2)
checks=0
with gzip.open("q9_port_followup_public191.txt.gz","rt") as f:
 for row in f:
    p=list(map(int,row.split()))
    assert len(p)==192 and len(set(p))==192 and all(0<=u<512 for u in p)
    assert all(((u^v).bit_count()==1)==(a+1==b) for b,v in enumerate(p) for a,u in enumerate(p[:b]))
    for d in range(9):
        ports={drop(u,d) for u,v in zip(p,p[1:]) if (u^v)==1<<d}
        n,inc,pairs=stats(ports)
        assert inc>=2*len(ports)-2
        assert n<=bound(191,len(ports)) and pairs>=pairmin(191,len(ports))
        checks+=1
print("witness/direction checks:",checks)
rng=random.Random(229)
for k in (20,24,25):
    nbr=[]
    for j in range(1000):
        available=list(range(256)); rng.shuffle(available); P=set()
        for u in available:
            if all((u^v).bit_count()>1 for v in P):P.add(u)
            if len(P)==k:break
        assert len(P)==k
        n,_,_=stats(P);nbr.append(n)
    print("k, bound at m=229, minimum sampled, passing:",k,bound(229,k),min(nbr),sum(v<=bound(229,k) for v in nbr))
for m in (229,226,221):
    k=m//9;print("m,k,empty,neighbor cap,pair floor",m,k,255-m+k,bound(m,k),pairmin(m,k))

cluster=[x for x in range(256) if x.bit_count()==2][:25]
print("cluster neighbors, available incidences, distance-two pairs:",stats(cluster))
