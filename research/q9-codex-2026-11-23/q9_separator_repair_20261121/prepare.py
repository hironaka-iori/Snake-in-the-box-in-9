import json,random,itertools,collections
from pathlib import Path
D=Path(__file__).resolve().parent;R=D.parent
words=(R/'q9_three_axis.in').read_text().splitlines()
NB=[{v^(1<<d) for d in range(9)} for v in range(512)]
def majority(w):
    p=[0]
    for d in map(int,w):p.append(p[-1]^(1<<d))
    return set(p[::2])
def graph(A):
    adj={v:set() for v in A}
    for q in range(512):
        L=A&NB[q]
        if len(L)==2:
            v,w=L;adj[v].add(w);adj[w].add(v)
    return adj
def parts(adj,cut):
    unseen=set(adj)-cut;bins=[]
    while unseen:
        comp=[unseen.pop()]
        for v in comp:
            nxt=unseen&adj[v];unseen-=nxt;comp+=sorted(nxt)
        bins.append(set(comp))
    return bins
def bridges(A,cut,comp,rng):
    group={v:i for i,p in enumerate(comp) for v in p};ends=set.union(*comp);L={q:NB[q]&A for q in range(512) if q.bit_count()%2==1}
    straight=[]
    for q,B in L.items():
        if len(B)<=2:continue
        for x,y in itertools.combinations(sorted(B&ends),2):
            if group[x]==group[y]:continue
            rem=B-{x,y}
            if not cut&rem and len(rem)<=6:straight.append(((q,),{x,y},rem,set()))
    bend=[]
    for z in range(512):
        if z.bit_count()%2 or z in A:continue
        routes=[(q,x,L[q]-{x}) for q in sorted(NB[z]) for x in sorted(L[q]&ends) if len(L[q])<=5]
        for (q,x,rx),(s,y,ry) in itertools.combinations(routes,2):
            if q==s or group[x]==group[y] or x in ry or y in rx:continue
            rem=rx|ry
            if rem&cut or not 1<=len(rem)<=6:continue
            bend.append(((q,s),{x,y},rem,{z}))
    def choose(items,count):
        ranked=sorted(((len(r[2]),rng.random(),r) for r in items),key=lambda h:h[:2])
        bycost=collections.defaultdict(list)
        for c,_,r in ranked:bycost[c].append(r)
        chosen=[]
        for depth in range(count):
            for k in sorted(bycost):
                if depth<len(bycost[k]):chosen.append(bycost[k][depth])
                if len(chosen)==count:return chosen
        return chosen
    first=choose(straight,18);joint=[]
    for b,h in itertools.combinations(first,2):
        if b[0]==h[0] or b[1]&h[1] or b[1]&h[2] or h[1]&b[2]:continue
        rm=b[2]|h[2]
        if len(rm)<=8:joint.append((b[0]+h[0],b[1]|h[1],rm,set()))
    return [('direct',g) for g in first[:3]]+[('via',g) for g in choose(bend,5)]+[('double',g) for g in choose(joint,3)]
def gen():
    jobs=[];fails=[]
    for line in (D/'cuts.txt').read_text().splitlines():
        _,row,edges,tips,ncomp,need,sz,*c=line.split();row,edges,tips,ncomp,need,sz=map(int,(row,edges,tips,ncomp,need,sz));C=set(map(int,c))
        A=majority(words[row]);adj=graph(A);groups=parts(adj,C);T={x for x in A if len(adj[x])==1}
        dem=[max(len(p&T),2-min(2,len(set.union(*(adj[x] for x in p))&C))) for p in groups]
        assert len(groups)==ncomp and sum(dem)+len(C&T)==need and (ncomp>len(C)+1 or need>2)
        cert=dict(row=row,cut=sorted(C),components=[sorted(p) for p in groups],leaves=sorted(T),demand=dem)
        fails.append(cert);rng=random.Random(10267+row)
        for gidx,(kind,(qs,ends,remove,added)) in enumerate(bridges(A,C,groups,rng)):
            targetA=ends|added;med=set(qs);noadd=set.union(*(NB[q] for q in qs))-targetA
            assert not (noadd & C) and (noadd&A)==remove
            force=(C|targetA);local=(ends|remove|added|C)
            old_choices=list(sorted(A-force-remove))
            def locality(x):return min((x^y).bit_count() for y in local)
            rng.shuffle(old_choices);old_choices.sort(key=locality)
            candidates=[x for x in range(512) if x.bit_count()%2==0 and x not in (A|noadd|added)]
            rng.shuffle(candidates);candidates.sort(key=lambda x:(locality(x),-sum(len((A-remove)&NB[q]) in (1,2) for q in NB[x])))
            for k in (5,8):
                if len(remove)>k:continue
                drop=remove|set(old_choices[:18 if k==5 else 30])
                new=added|set(candidates[:28 if k==5 else 45])
                assert len(drop)>=k and len(new)>=k
                jobs.append(dict(row=row,kind=kind,qs=list(qs),ends=sorted(ends),cut=sorted(C),remove=sorted(remove),added=sorted(added),k=k,drop=sorted(drop),new=sorted(new)))
    (D/'certificates.jsonl').write_text(''.join(json.dumps(c,separators=(',',':'))+'\n' for c in fails))
    (D/'jobs.jsonl').write_text(''.join(json.dumps(c,separators=(',',':'))+'\n' for c in jobs))
    print(json.dumps(dict(roots=len(fails),jobs=len(jobs),kinds=dict(collections.Counter(x['kind'] for x in jobs)),sample=fails[0])))
if __name__=='__main__':gen()
