from itertools import combinations
from pathlib import Path
import json

def norm(w):
    book={}
    return ''.join(str(book.setdefault(a,len(book))) for a in w)

def donors(size):
    words=Path('q8_single_cross_complete_arms.txt').read_text().split()
    words.extend(l.split()[-1] for l in Path('q8_mother_search_20261120/mothers.tsv').read_text().splitlines()[1:])
    out=set()
    for w in words:
        for i in range(len(w)-size+1):
            t=w[i:i+size];out.add(min(norm(t),norm(t[::-1])))
    return sorted(out)

def path(w):
    p=[0]
    for a in w:p.append(p[-1]^(1<<int(a)))
    return p

def cases(p):
    base=set(p);inside=set(p[1:-1])
    possible=sorted(x for x in set(range(256))-base if all(x^1<<d not in inside for d in range(8)))
    for m in range(1<<len(possible)):
        added=tuple(x for i,x in enumerate(possible) if m>>i&1);low=base|set(added)
        adj={x:{x^1<<d for d in range(8)}&low for x in low}
        if any(len(a)>2 for a in adj.values()):continue
        unseen=set(low);comp=[];cycle=False
        while unseen:
            start=unseen.pop();q=[start];vertices=set(q)
            while q:
                y=q.pop();new=adj[y]&unseen;q.extend(new);vertices.update(new);unseen-=new
            cycle|=all(len(adj[y])==2 for y in vertices);comp.append(vertices)
        if cycle:continue
        iso={x for x in low if not adj[x]};tips={x for x in low if len(adj[x])==1}
        for l in range(min(2-len(iso),len(tips))+1):
            for unmatched in combinations(sorted(tips),l):
                low_ends=set(unmatched)|iso;ports=(tips-set(unmatched))|iso
                if any(not (ports&part) for part in comp):continue
                for full in [(2,0),(1,1),(0,2)]:
                    ends=[full[h]-sum(x.bit_count()%2==h for x in low_ends) for h in [0,1]]
                    if min(ends)<0:continue
                    delta=sum((-1)**x.bit_count() for x in low)-(full[0]-full[1])//2
                    yield added,tuple(sorted(ports)),full,ends,delta

def run(job):
    from certify_q9_intact_q8_facet import build
    import random
    w,case,parts=job;p=path(w);added,ports,full,ends,delta=case;low=set(p)|set(added)
    axes=list(combinations(range(8),3));random.Random(403215).shuffle(axes)
    res=build(p,ports,low,ends,delta,axes[:parts])
    if res is None:return dict(word=w,added=added,ports=ports,full=full,empty=True)
    const,scale,tables,c=res;num=const+sum(t[0][2] for _,t in tables)
    bound=len(low)-1+num//scale;bound-=int(bound%2!=full[0]%2)
    return dict(word=w,added=added,ports=ports,full=full,ends=ends,delta=delta,numerator=num,bound=bound,cert=c)

if __name__=='__main__':
    import sys,gzip
    from concurrent.futures import ProcessPoolExecutor
    n,parts,workers=map(int,sys.argv[1:4]);words=donors(n)
    jobs=[(w,c,parts) for w in words for c in cases(path(w))]
    with gzip.open(sys.argv[4],'wt') as f,ProcessPoolExecutor(workers) as pool:
        for j,r in enumerate(pool.map(run,jobs,chunksize=1)):
            f.write(json.dumps(r,separators=(',',':'))+'\n');f.flush()
            print(j,r['word'],r.get('bound','EMPTY'),flush=True)
    print('DONE',len(words),len(jobs),flush=True)
