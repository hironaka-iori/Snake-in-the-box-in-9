from pathlib import Path
from itertools import accumulate,combinations
from functools import lru_cache
from operator import xor
from collections import defaultdict,Counter
import random,json,sys
D=Path(__file__).resolve().parent;R=D.parent
words=(R/'q9_gap_generations/prior191.words').read_text().splitlines()
def verts(w):return list(accumulate([1<<int(d) for d in w],xor,initial=0))
bank=[verts(w) for w in words]
def bits(x):
    out=0
    for v in x:out|=1<<v
    return out
def unpack(x):return {k for k in range(512) if x>>k&1}
ball=[bits([v]+[v^(1<<j) for j in range(9)]) for v in range(512)]
def halo(seq):
    b=0
    for v in seq:b|=ball[v]
    return b
def canon(w):
    def f(s):
        d={};return tuple(d.setdefault(c,len(d)) for c in s)
    return min(f(w),f(w[::-1]))
@lru_cache(None)
def hostshapes(r,size):return {canon(words[r][i:i+size]) for i in range(192-size)}
def check(p):
    assert len(set(p))==len(p) and all(0<=v<512 for v in p)
    assert all(((x^p[j]).bit_count()==1)==(i+1==j) for i,x in enumerate(p) for j in range(i+1,len(p)))
def transform(v,perm):return sum(1<<d for i,d in enumerate(perm) if v>>i&1)
def graft(line,idx):
    _,r,z,a,b,s,e,m,c=line.split();r,z,a,b,s,e,c=map(int,(r,z,a,b,s,e,c));m=tuple(map(int,m));h=bank[r];don=bank[z]
    assert z!=r and sorted(m)==list(range(9));seg=don[s:e+1] if s<e else don[e:s+1][::-1]
    path=[h[a]^transform(v^seg[0],m) for v in seg]
    assert path[-1]==h[b] and (h[a]^h[b]).bit_count()==(don[s]^don[e]).bit_count()
    n=abs(s-e);gain=n-(b-a);assert gain in (2,4,6,8) and canon(words[z][min(s,e):max(s,e)]) not in hostshapes(r,n)
    clash=halo(path[1:-1]);conf=list(i for i,v in enumerate(h) if not a<=i<=b and clash>>v&1)
    assert len(conf)==c
    return dict(id=idx,row=r,z=z,a=a,b=b,g=gain,mask=bits(path),halo=halo(path),conf=bits(conf),cost=c)
def spec(G,holes,rng,seedset=None):
    h=bank[G[0]['row']];a=set();clash=0;inner=set();protected=0
    for g in G:protected|=g['mask'];clash|=g['conf'];inner.update(range(g['a'],g['b']+1))
    keep={i for i in range(192) if i not in inner and not clash>>i&1};before=len(keep)
    # Redistribute released positions across the length, including independent remote holes.
    remote=[];choices=[i for i in sorted(keep) if all(abs(i-j)>7 for g in G for j in (g['a'],g['b']))]
    rng.shuffle(choices);starts=[]
    for center in choices:
        if len(starts)>=2:break
        if all(abs(center-j)>13 for j in starts) and holes>=6:
            starts.append(center)
            for i in (center-1,center,center+1):
                if i in keep:keep.remove(i);remote.append(i)
    candidates=list(sorted(keep));rng.shuffle(candidates)
    for i in candidates:
        if before-len(keep)>=holes:break
        length=rng.randrange(2,6)
        for j in range(i,i+length):
            if j in keep:keep.remove(j)
            if before-len(keep)>=holes:break
    fixed=protected|bits(h[i] for i in keep)
    return dict(grafts=[g['id'] for g in G],row=G[0]['row'],gains=[g['g'] for g in G],conflicts=192-len(inner)-before,holes=before-len(keep),remote=remote,protected=hex(protected),fixed=hex(fixed))
def main():
    rng=random.Random(791033);assert len(bank)==131
    for p in bank:check(p)
    data=[graft(l,i) for i,l in enumerate((D/'grafts.txt').read_text().splitlines())];by=defaultdict(list)
    for g in data:by[g['row']].append(g)
    single=[];dual=[]
    for row,G in by.items():
        for gain in (2,4,6,8):
            source=[(g['cost'],rng.random(),g) for g in G if g['g']==gain]
            if source:single.append([min(source,key=lambda r:r[:2])[2]])
        pool=[]
        for x,y in combinations(G,2):
            if x['z']==y['z'] or (x['halo']&y['mask']):continue
            if not(x['b']+7<y['a'] or y['b']+7<x['a']):continue
            cutmask=((1<<(x['b']-x['a']+1))-1)<<x['a'] | ((1<<(y['b']-y['a']+1))-1)<<y['a']
            c=((x['conf']|y['conf'])&~cutmask).bit_count()
            pool.append((c,rng.random(),x,y))
        pool.sort(key=lambda v:v[:2]);used=set()
        for _,__,x,y in pool:
            if x['id'] in used or y['id'] in used:continue
            dual.append([x,y]);used.update((x['id'],y['id']))
            if len(used)>=6:break
    rng.shuffle(single);rng.shuffle(dual)
    for label,proposals in [('single',single),('double',dual)]:
        with (D/f'{label}.jsonl').open('w') as f:
            for j,G in enumerate(proposals):
                for holes in (0,12,32):
                    a=spec(G,holes,random.Random(497*j+holes+1));a['case']=j
                    print(json.dumps(a,separators=(',',':')),file=f)
    print(json.dumps(dict(checked_grafts=len(data),source_rows=len(by),single=len(single),double=len(dual),single_conflict_counts=dict(Counter(g[0]['cost'] for g in single)))))
if __name__=='__main__':main()
