from collections import Counter,defaultdict
from pathlib import Path
from itertools import chain
from functools import lru_cache
import random,json,hashlib
D=Path(__file__).resolve().parent;R=D.parent
CUBE=set(range(512));NB=[{x^1<<d for d in range(9)} for x in range(512)]
def paircheck(p):
    assert len(p)==len(set(p)) and all(0<=v<512 for v in p) and all(((a^p[j]).bit_count()==1)==(j==i+1) for i,a in enumerate(p) for j in range(i+1,len(p)))
def components(S):
    rest=set(S); groups=[]
    while rest:
        todo=[rest.pop()]
        for x in todo:
            for y in NB[x]&rest:rest.remove(y);todo.append(y)
        groups.append(todo)
    return groups
def ashex(s):return hex(sum(1<<v for v in s))
def unhex(s):
    b=int(s,16);return {v for v in range(512) if b>>v&1}
def select(a,b,n,rng,mode):
    routes=[a,b];S=set(a+b);pos={v:(i,j) for i,p in enumerate(routes) for j,v in enumerate(p)}
    cross=sorted(set(a)&{v-256 for v in b});rng.shuffle(cross)
    protect=set()
    for idx,x in enumerate(cross):
        if mode%2 and idx<1+int(mode==3):
            for y in [x,x+256]:
                i,j=pos[y];p=routes[i]
                near=[p[k] for k in (j-1,j+1) if 0<=k<len(p)]
                if len(near)==2:S.discard(rng.choice(near))
                protect.add(y)
        else:S.discard(x+256*rng.randrange(2))
    for g in components(S):
        if all(len(S&NB[v])==2 for v in g):S.remove(rng.choice(g))
    assert all(len(NB[v]&S)<=2 for v in S)
    while len(S)>n:
        starts=[]
        if mode in (0,1) and rng.random()<.74:
            starts=[v for v in S-protect if len(NB[v]&S)<=1]
        if not starts:
            if mode in (2,3) and rng.random()<.72:
                y=rng.choice(cross);i=rng.randrange(2);p=routes[i];center=pos[y+256*i][1]
                starts=[p[k] for k in range(max(0,center-15),min(len(p),center+16)) if p[k] in S-protect]
            if not starts:starts=sorted(S-protect)
        v=rng.choice(sorted(starts));i,j=pos[v];p=routes[i];direction=rng.choice([-1,1]);dist=rng.randint(2,9)
        for h in range(dist):
            k=j+h*direction
            if not 0<=k<len(p) or p[k] in protect:break
            S.discard(p[k])
            if len(S)==n:break
    assert len(S)==n and all(len(NB[v]&S)<=2 for v in S)
    groups=components(S);assert all(sum(len(NB[v]&S) for v in g)//2==len(g)-1 for g in groups)
    return S,len(groups)

def run():
    bank={};clusters={}
    for l in (R/'q8_registered_donor_clusters.txt').open():
        group,idx,*p=map(int,l.split());paircheck(p);assert max(p)<256 and idx not in bank
        bank[idx]=p;clusters[idx]=group
    @lru_cache(maxsize=20000)
    def right(idx,perm):
        m=[1<<int(d) for d in perm];assert sorted(perm)==list('01234567')
        return tuple(sum(m[d] for d in range(8) if v>>d&1) for v in bank[idx])
    @lru_cache(maxsize=20000)
    def shifted(a,t):return frozenset(v^t for v in bank[a])
    strata=defaultdict(list);total=0
    for ln,l in enumerate((R/'q8_near_host_placements.log').open(),1):
        if not l.startswith('HOST '):continue
        _,a,b,t,count,pm=l.split();a,b,t,count=map(int,[a,b,t,count]);pp=right(b,pm)
        assert len(shifted(a,t).intersection(pp))==count
        strata[count].append((ln,a,b,t,count,pm));total+=1
    assert total==106435
    rng=random.Random(129531);selected=[]
    for k,rows in sorted(strata.items()):
        rng.shuffle(rows);chosen={};clusterpairs=set();donorpairs=set()
        for r in rows:
            ln,a,b,*_=r;pair=(clusters[a],clusters[b])
            if pair not in clusterpairs:chosen[ln]=r;clusterpairs.add(pair);donorpairs.add((a,b))
            if len(chosen)>=60:break
        for r in rows:
            if len(chosen)>=60:break
            ln,a,b,*_=r
            if (a,b) not in donorpairs:chosen[ln]=r;donorpairs.add((a,b))
        for r in rows:
            if len(chosen)>=60:break
            chosen[r[0]]=r
        selected+=list(chosen.values())
    rng.shuffle(selected);seen=set();counts=Counter();modes=Counter()
    with (D/'cases.jsonl').open('w') as dest:
        for ln,a,b,t,k,pm in selected:
            aseq=bank[a];bseq=[256+(v^t) for v in right(b,pm)];host=set(aseq+bseq)
            assert sum(v+256 in host for v in aseq)==k
            for ix,n in enumerate((145,154,164,173)):
                for side in (0,1):
                    mode=(ix+side*2+ln)%4
                    fixed,cc=select(aseq,bseq,n,rng,mode);h=ashex(fixed)
                    if h in seen:continue
                    seen.add(h);counts[n]+=1;modes[mode]+=1
                    print(json.dumps(dict(line=ln,aid=a,bid=b,t=t,perm=pm,overlap=k,anchors=n,rule=mode,components=cc,fixed=h,host=ashex(host)),separators=(',',':')),file=dest)
    print(json.dumps(dict(donors=len(bank),placements=total,overlaps={k:len(v) for k,v in strata.items()},selected=len(selected),strata=Counter(r[4] for r in selected),distinct_fixed=len(seen),anchor_sizes=counts,rules=modes,source_sha256=hashlib.sha256((R/'q8_near_host_placements.log').read_bytes()).hexdigest()),indent=2))
if __name__=='__main__':run()
