"""Generate several independently rerouted pieces of one two-chord walk."""
from pathlib import Path
from itertools import combinations
from functools import lru_cache
from collections import Counter
import random,json,sys
D=Path(__file__).resolve().parent
N=tuple(tuple(x^1<<k for k in range(9)) for x in range(512))
B=tuple(sum(1<<v for v in z) for z in N);ALL=(1<<512)-1
def mask(vs):return sum(1<<v for v in set(vs))
def decode(b):
    while b:
        x=b&-b;yield x.bit_length()-1;b-=x
def points(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    return p
def chords(p):
    old={};out=[]
    for i,v in enumerate(p):
        if v in old:return None
        for x in N[v]:
            if x in old and old[x]+1<i:out.append((old[x],i))
        old[v]=i
    return out
def norm(w):
    def one(s):
        t={};return ''.join(str(t.setdefault(x,len(t))) for x in s)
    return min(one(w),one(w[::-1]))
def inputs(typ):
    if typ=='target':
        seen=set()
        for i,w in enumerate((D.parent/'q9_three_axis.in').read_text().split()):
            p=points(w);ch=chords(p)
            if ch and len(ch)==2 and all(a>0 and b<len(p)-1 for a,b in ch) and norm(w) not in seen:
                seen.add(norm(w));yield i,p,ch,[]
    else:
        for i,w in enumerate((D.parent/'q9_gap_generations/prior191.words').read_text().split()):
            p=points(w);old=set(p);rr=random.Random(6283+i);cs=[]
            for j in range(6,len(p)-6):
                q=p[:];q[j]=p[j-1]^p[j]^p[j+1]
                if q[j] in old:continue
                ch=chords(q)
                if ch and len(ch)==1 and all(0<a<b<len(p)-1 for a,b in ch):cs.append(j)
            rr.shuffle(cs)
            for a,b in combinations(cs,2):
                if abs(a-b)<20:continue
                q=p[:]
                for j in (a,b):q[j]=p[j-1]^p[j]^p[j+1]
                ch=chords(q)
                if ch and len(ch)==2 and len(set(sum((list(x) for x in ch),[])))==4:
                    yield i,q,ch,sorted([a,b]);break
def segments(indices,n):
    ids=sorted(set(t for t in indices if 0<=t<n));rs=[]
    for t in ids:
        if rs and rs[-1][1]+1>=t:rs[-1][1]=t
        else:rs.append([t,t])
    return rs
def construct(p,src,ch,known,version,seed):
    r=random.Random(seed+34137*src+23117*version);n=len(p);S=set(p);sm=mask(S)
    if known: sites=known[:]
    else:
        opts=[(a,b) for a in ch[0] for b in ch[1]]
        r.shuffle(opts);sites=list(opts[version%4])
    ranges=[];broad=version//4
    for v in sites:
        rad=(2 if known else 1)+r.randrange(3+broad*2)
        ranges.extend(range(v-rad,v+rad+1+r.randrange(2)))
    if not known and version%3==1:
        v=r.choice([t for t in range(5,n-5) if min(abs(t-x) for x in sites)>8]);ranges.extend(range(v-3,v+4))
    if version%3==2 or broad>=2:
        tip=3+r.randrange(6);ranges.extend(range(tip));ranges.extend(range(n-tip,n))
    if broad>=1:
        v=r.choice([t for c in ch for t in c]);ranges.extend(range(v-4,v+5))
    holes=segments(ranges,n);F={p[i] for i in range(n) if not any(a<=i<=b for a,b in holes)}
    ds=[len(F.intersection(N[v])) for v in F]
    if any(d>2 for d in ds):return None
    ports=[];tasks=[]
    for a,b in holes:
        u=p[a-1] if a>0 else None;v=p[b+1] if b<n-1 else None
        ports+=([u] if u is not None else [])+([v] if v is not None else [])
        if u is None:u,v=v,None
        tasks.append((u,v,min(23,b-a+2+4),False))
    r.shuffle(ports)
    cross=[(u,v, min(20,11+broad*3),True) for u,v in combinations(ports,2) if not any({u,v}=={a,b} for a,b,_,_ in tasks)]
    r.shuffle(cross);tasks.extend(cross[:4+broad*3])
    freq=[len(F.intersection(N[v])) for v in range(512)]
    groups=[];rawRoutes=[];budget=2400+1300*broad
    for ix,(u,v,maxdepth,is_cross) in enumerate(tasks):
        if u is None:continue
        dom={x for x in range(512) if x not in F and freq[x]==int(x in N[u])+int(v is not None and x in N[v])}
        domB=mask(dom);orders=list(range(9));r.shuffle(orders);queue=[u];found=0;new=set();sample=[];steps=0
        def walk(x,blocked,depth):
            nonlocal found,steps
            if steps>=budget or found>=85:return
            steps+=1
            dx=0 if v is None else (x^v).bit_count()
            if dx>maxdepth-depth:return
            if v is not None and dx==1 and depth:
                found+=1;new.update(queue[1:])
                if len(sample)<8:sample.append(queue[1:]+[v])
                return
            if v is None and depth>=max(2,maxdepth//3):
                found+=1;new.update(queue[1:])
                if len(sample)<8:sample.append(queue[1:])
            if depth>=maxdepth-(v is not None):return
            cand=[x^1<<k for k in orders if (domB>> (x^1<<k))&1 and not (blocked>>(x^1<<k))&1]
            if v is not None and depth>2 and steps%7<=2:cand.sort(key=lambda y:(y^v).bit_count())
            for y in cand:
                queue.append(y);walk(y,blocked|B[x]|1<<x,depth+1);queue.pop()
                if steps>=budget or found>=85:return
        walk(u,0,0)
        groups.append(dict(ports=[u,v],cross=is_cross,routes=found,nodes=steps,cap=steps>=budget or found>=85,extra=sorted(new-S),example=sample[:1]))
    hard=sorted(F);return dict(src=src,version=version,raw=p,chords=ch,holes=holes,hard=hard,groups=groups,changed=known)
def main():
    typ,lo,hi,offset,vcount=sys.argv[1:6];lo,hi,offset,vcount=map(int,(lo,hi,offset,vcount))
    ds=list(inputs(typ));random.Random(719281).shuffle(ds)
    for idx,(i,p,ch,z) in enumerate(ds[lo:hi],lo):
        for ver in range(offset,offset+vcount):
            rec=construct(p,i,ch,z,ver,913658)
            if rec is not None:
                rec['rank']=idx;print(json.dumps(rec,separators=(',',':')),flush=True)
if __name__=='__main__':main()
