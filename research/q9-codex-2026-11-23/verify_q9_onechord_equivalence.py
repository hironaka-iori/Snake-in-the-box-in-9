"""Exhibit coordinate maps and translations for matching parity sets, with explicit recheck."""
import itertools, json
from collections import defaultdict
from pathlib import Path
def fingerprint(side):
    hist=[0]*512
    for a,b in itertools.combinations(side,2):hist[a^b]+=1
    return tuple(tuple(sorted(hist[v] for v in range(1,512) if v.bit_count()==k)) for k in (2,4,6,8))
def rooted(side,r):
    diff=[v^r for v in side]
    return tuple(tuple(sum(1 for x in diff if x&(1<<i) and x.bit_count()==w) for w in (2,4,6,8)) for i in range(9))
def iso(source,target):
    a=source[0]; ds=rooted(source,a)
    pattern=sorted(ds)
    lookup=set(target)
    for b in target:
        dt=rooted(target,b)
        if sorted(dt)!=pattern:continue
        dims=sorted(set(ds))
        A=[[i for i in range(9) if ds[i]==t] for t in dims]
        B=[[i for i in range(9) if dt[i]==t] for t in dims]
        for groups in itertools.product(*(itertools.permutations(g) for g in B)):
            perm=[0]*9
            for left,right in zip(A,groups):
                for i,j in zip(left,right):perm[i]=j
            def apply(v):return sum((1<<j) for i,j in enumerate(perm) if (v>>i)&1)
            shift=b^apply(a)
            if all(apply(v)^shift in lookup for v in source):
                assert len(set(perm))==9 and {shift^sum(((v>>i)&1)<<perm[i] for i in range(9)) for v in source}==lookup
                return dict(perm=perm,shift=shift)
    return None
if __name__=="__main__":
    old=[tuple(map(int,l.split())) for l in open("q9_onechord_minority_sets.txt")]
    banks=defaultdict(list)
    for i,s in enumerate(old):banks[fingerprint(s)].append(i)
    maps=[];distinct=0
    for index,line in enumerate(open("q9_face_donor_walks.txt")):
        p=list(map(int,line.split())); used=set(p)
        if sum((v^(1<<k)) in used for v in p for k in range(9))//2!=len(p):continue
        s=tuple(sorted(p[1::2]))
        for i in banks[fingerprint(s)]:
            relation=iso(s,old[i])
            if relation:maps.append(dict(row=index,old_row=i,**relation));break
        else:distinct+=1
    print(json.dumps(dict(matched=len(maps),unmatched=distinct,maps=maps)))
