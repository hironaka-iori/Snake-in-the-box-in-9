"""Recover all two-face colourings of a prescribed projection from its cut-degree parity."""
import argparse
from collections import Counter
from itertools import combinations
from pathlib import Path
from solve import defects,save


def bits(word):
    while word:
        low=word&-word;yield low.bit_length()-1;word^=low


def reduce_system(rows,n):
    """Express every solution as a particular endpoint response plus a kernel vector."""
    coeff=(1<<n)-1;piv={};conditions=[]
    for left,right in rows:
        row=left|(right<<n)
        while left:=row&coeff:
            k=(left&-left).bit_length()-1
            if k not in piv:piv[k]=row;break
            row^=piv[k]
        else:
            if row:conditions.append(row>>n)
    for k in sorted(piv,reverse=True):
        for j in piv:
            if j<k and piv[j]>>k&1:piv[j]^=piv[k]
    # Column n represents the affine constant; the other RHS columns represent
    # singleton endpoints. One magnitude-independent reduction serves all pairs.
    response=[0]*(n+1);signature=[0]*(n+1);kernel=[]
    for k,row in piv.items():
        for j in bits(row>>n):response[j]|=1<<k
    for i,condition in enumerate(conditions):
        for j in bits(condition):signature[j]|=1<<i
    for j in range(n):
        if j not in piv:kernel.append((1<<j)|sum(1<<k for k,row in piv.items() if row>>j&1))
    return response,signature,kernel


def decide(projection,doubled,d,limit=None,count_all=False,collect_paths=False):
    W=set(projection);R=set(doubled);assert R<=W and len(W)+len(R)>=3
    def reject(reason):return dict(status="EXHAUSTED",reason=reason,examined=0,solutions=0)
    adj={v:{v^(1<<j) for j in range(d)}&W for v in W}
    if any(not 1<=len(adj[r])<=2 or adj[r]&R for r in R):return reject("doubled degree")
    root_ends=[r for r in R if len(adj[r])==1];needed=2-len(root_ends)
    if needed<0:return reject("too many tips")
    if max(sum(v.bit_count()%2==p for v in W) for p in (0,1))>(len(W)+1)//2:return reject("projected parity")
    sites=sorted(W-R);n=len(sites);index={v:i for i,v in enumerate(sites)}
    if not sites:return reject("only doubled sites")
    ns=[sum(1<<index[u] for u in adj[v]-R) for v in sites]
    crossing=[len(adj[v]&R) for v in sites]
    if max(crossing)>2:return reject("crossing degree")
    const=1<<n;rows=[]
    for i,u in enumerate(ns):
        rows.append((u^((1<<i) if u.bit_count()%2 else 0),(1<<i)^(const if crossing[i]%2 else 0)))
    for r in R:
        if len(adj[r])==2:rows.append((sum(1<<index[x] for x in adj[r]),const))
    rows.append((1,0)) # exchange the two complete faces to force the first phase zero
    response,sig,kernel=reduce_system(rows,n)
    eligible=[i for i,m in enumerate(crossing) if m<=1]
    parity=[v.bit_count()%2 for v in sites]
    # A projected complete path has len(W) nodes. Its two endpoint colours
    # determine their required count of even base addresses.
    expected_even=2*sum(v.bit_count()%2==0 for v in W)-len(W)+1
    even_needed=expected_even-sum(r.bit_count()%2==0 for r in root_ends)
    if not 0<=even_needed<=needed:return reject("endpoint parity")
    endpoint_sets=[]
    if needed==2:
        buckets={}
        for i in eligible:
            for j in buckets.get(sig[n]^sig[i],()):
                if int(not parity[i])+int(not parity[j])==even_needed:endpoint_sets.append((j,i))
            buckets.setdefault(sig[i],[]).append(i)
    elif needed==1:endpoint_sets=[(i,) for i in eligible if sig[i]==sig[n] and int(not parity[i])==even_needed]
    elif not sig[n]:endpoint_sets=[()]
    tested=solutions=0;witness=None;paths=[]
    # Try high-degree sites first; parity already prescribes the allowed positive degree exactly.
    order=sorted(range(n),key=lambda i:(crossing[i]+ns[i].bit_count(),crossing[i]),reverse=True)
    def result(status):
        out=dict(status=status,dimension=len(kernel),compatible_endpoint_sets=len(endpoint_sets),
                 examined=tested,solutions=solutions,path=witness)
        if collect_paths:out["paths"]=paths
        return out
    for ends in endpoint_sets:
        z=response[n]
        for i in ends:z^=response[i]
        for step in range(1<<len(kernel)):
            if limit is not None and tested>=limit:return result("OPEN")
            if step:z^=kernel[(step&-step).bit_length()-1]
            tested+=1
            for i in order:
                h=(ns[i]&z).bit_count()
                if z>>i&1:h=ns[i].bit_count()-h
                if not 1<=h+crossing[i]<=2:break
            else:
                qset={v|(((z>>i&1)^parity[i])<<d) for i,v in enumerate(sites)}
                for r in R:qset.update((r,r|(1<<d)))
                hood={v:{v^(1<<j) for j in range(d+1)}&qset for v in qset}
                tips=[v for v,nb in hood.items() if len(nb)==1]
                assert len(tips)==2 and all(len(nbr)<=2 for nbr in hood.values())
                q=[tips[0]];seen=set(q)
                while fresh:=hood[q[-1]]-seen:
                    assert len(fresh)==1;v=fresh.pop();q.append(v);seen.add(v)
                if len(q)==len(qset):
                    assert not defects(q)
                    solutions+=1
                    if collect_paths:paths.append(q)
                    if witness is None:witness=q
                    if not count_all:return result("FOUND")
    return result("FOUND" if solutions else "EXHAUSTED")


def control():
    # Enumerate genuine paths directly in Q4, then compare counts for every
    # one of the 3^8 possible absent/single/doubled assignments on Q3.
    actual={};seen=set()
    def grow(q):
        s=frozenset(q)
        if len(q)>=3 and s not in seen:
            seen.add(s);w=frozenset(v&7 for v in s);r=frozenset(v for v in w if v in s and (v|8) in s)
            actual[w,r]=actual.get((w,r),0)+1
        for j in range(4):
            v=q[-1]^(1<<j)
            if v not in s and all((v^u).bit_count()!=1 for u in q[:-1]):grow(q+[v])
    for v in range(16):grow([v])
    from itertools import product
    tested=0
    for assignment in product(range(3),repeat=8):
        w=frozenset(i for i,s in enumerate(assignment) if s);r=frozenset(i for i,s in enumerate(assignment) if s==2)
        if len(w)+len(r)<3:continue
        z=decide(w,r,3,count_all=True);assert 2*z["solutions"]==actual.get((w,r),0),(w,r,z,actual.get((w,r),0))
        tested+=1
    return dict(projections=tested,distinct_Q4_path_sets=len(seen))


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--control",action="store_true");a=p.parse_args()
    if a.control:
        r=control();save(Path("fibre-laplacian-control.json"),r);print(r)
