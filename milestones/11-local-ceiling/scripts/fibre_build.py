"""Build the alternating-fibre union of cycles in Q9 from a disjoint pair (A,B) in Q_a, verify it,
and report identity data and the (shape, counts) windows it realizes."""
import json, sys, itertools, collections
d=json.load(open(sys.argv[1])); a=d['a']; A=set(d['A']); B=set(d['B']); b=9-a
S=set()
for y in range(1<<b):
    for u in (A if bin(y).count('1')%2==0 else B): S.add(u | (y<<a))
deg={x:sum(1 for k in range(9) if x^1<<k in S) for x in S}
assert all(v==2 for v in deg.values())
# cycles as ordered vertex lists
seen=set(); cycles=[]
for s in sorted(S):
    if s in seen: continue
    cyc=[s]; seen.add(s); prev=None; cur=s
    while True:
        nx=[w for w in (cur^1<<k for k in range(9)) if w in S and w!=prev]
        nxt=nx[0] if nx[0] not in seen or len(cyc)>2 and nx[0]==s else nx[-1]
        if nxt==s or nxt in seen: break
        cyc.append(nxt); seen.add(nxt); prev,cur=cur,nxt
    cycles.append(cyc)
pairs=list(itertools.combinations(range(9),2))
alpha={x:sum(1 for i,j in pairs if not({x^1<<i,x^1<<j,x^1<<i^1<<j}&S)) for x in S}
s0=sum(1 for v in range(512) for i,j in pairs if not(v>>i&1 or v>>j&1) and not({v,v|1<<i,v|1<<j,v|1<<i|1<<j}&S))
T=sum(alpha.values()); v=len(S)
print(f"|S|={v} cycles={collections.Counter(len(c) for c in cycles)} T={T} s0={s0} T+2s0={T+2*s0} 9216-35v={9216-35*v} meanalpha={T/v:.3f}")
def canon(ds):
    m={}; return tuple(m.setdefault(x,len(m)) for x in ds)
wins=collections.Counter()
for c in cycles:
    L=len(c)
    for k in (3,4):
        for st in range(L):
            vs=[c[(st+i)%L] for i in range(k+2)]
            ds=[(vs[i]^vs[i+1]).bit_length()-1 for i in range(k+1)]
            cs=tuple(min(alpha[x],6) for x in vs[1:-1])
            wins[(canon(ds),cs)]+=1
json.dump({'S':sorted(S),'cycles':cycles,'windows':[[list(k[0]),list(k[1]),n] for k,n in wins.items()]}, open(sys.argv[2],'w'))
print("distinct windows:", len(wins), " alpha distribution:", sorted(collections.Counter(alpha.values()).items()))
