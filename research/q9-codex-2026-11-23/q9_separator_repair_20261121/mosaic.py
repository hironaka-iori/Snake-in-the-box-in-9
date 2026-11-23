import itertools,json,random
from prepare import D,R,NB,graph,words,parts,majority
from solve import solve
from connect import repair
rng=random.Random(31492)
seps=list(map(json.loads,(D/'certificates.jsonl').read_text().splitlines()))
pool={}
for row,w in enumerate(words):
    A=frozenset(majority(w))
    if A in pool:continue
    pool[A]=(row,None)
for S,(row,_) in list(pool.items()):
    a=graph(S);tips={v for v in S if len(a[v])==1}
    if len(parts(a,set()))!=1 or len(tips)>2:del pool[S];continue
    pool[S]=(row,a,tips)
def within(target,c):
    a=graph(target);C=set(c['cut']);g=parts(a,C);tips={v for v in target if len(a[v])==1}
    need=sum(max(len(z&tips),2-min(2,len(set.union(*(a[x] for x in z))&C))) for z in g)+len(C&tips)
    return len(g)<=len(C)+1 and need<=2 and len(parts(a,set()))==1
def plans():
    for cert in seps:
        r=cert['row'];A=majority(words[r]);C=set(cert['cut']);group={v:i for i,ls in enumerate(cert['components']) for v in ls}
        ranked=sorted(((len(A-B),rr,B,G,tips) for B,(rr,G,tips) in pool.items() if C<=B and B!=A),key=lambda a:a[:2])
        kept=0
        for distance,rr,B,G,bt in ranked:
            if not 2<=distance<=52 or not within(B,cert):continue
            contact=None
            for q in sorted(set.union(*(NB[x] for x in A-B))):
                pair=B&NB[q]
                if len(pair)!=2 or not pair<=A-C:continue
                x,y=pair
                if group[x]!=group[y]:contact=([q],pair,set());break
            if contact is None:
                for z in sorted(B-A):
                    nbr=sorted(G[z]&(A-C))
                    for x,y in itertools.combinations(nbr,2):
                        if group[x]==group[y]:continue
                        q=next(q for q in sorted(NB[z]&NB[x]) if NB[q]&B=={x,z})
                        h=next(h for h in sorted(NB[z]&NB[y]) if NB[h]&B=={y,z})
                        contact=([q,h],{x,y},{z});break
                    if contact:break
            if not contact:continue
            qs,ends,add=contact;rm=set.union(*(NB[q] for q in qs))&(A-B)
            band=(B-A)-set.union(*(NB[q] for q in qs))|add
            if len(band)!=distance:continue
            start=max(1,len(rm),len(add));ks=sorted({start,(start+distance)//2,distance-1})
            for k in ks:
                if k<start:continue
                yield dict(row=r,donor=rr,qs=qs,cut=sorted(C),ends=sorted(ends),remove=sorted(rm),added=sorted(add),drop=sorted(A-B),new=sorted(B-A),k=k,distance=distance)
            kept+=1
            if kept>=2:break
def main():
    pp=list(plans())
    (D/'mosaic_plans.jsonl').write_text(''.join(json.dumps(c,separators=(',',':'))+'\n' for c in pp))
    for i,c in enumerate(pp):
        A=majority(words[c['row']]);s,n,conf,w=solve(A,c,12000)
        if w:print(json.dumps([i,s,w,None]),flush=True);return
        # The sorted donor set gives a known complete repair at distance d.
        # A strict submix must have distance below d and is solved independently.
        sr,B=repair(A,c,4500)
        print(json.dumps([i,s,sr,B],separators=(',',':')),flush=True)
if __name__=='__main__':main()
