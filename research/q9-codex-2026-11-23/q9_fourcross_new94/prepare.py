from pathlib import Path
from collections import Counter
D=Path(__file__).resolve().parent;B=D.parent/'q9_two_upper_free9495_20261121/reroutes/move'
def path(w,x=0):
    p=[x]
    for c in w:p.append(p[-1]^1<<int(c))
    return p
N=[{v^1<<j for j in range(8)} for v in range(256)]
out=[];seeds=[];trim=[]
for rec,mother in zip((B/'direct.dat').read_text().splitlines(),(B/'donors.words').read_text().split()):
    i,a,b=rec.split();p=path(mother);u=path(a);v=path(b,p[-1]);seeds.append(' '.join(map(str,[i,len(p),*p,len(u),*u,len(v),*v])))
    for n in (92,93):
        for st in range(95-(n+1)+1):
            g=p[st:st+n+1];f=set(range(256))-set(g)-set.union(*(N[x] for x in g))
            trim.append((i,n,st,len(f),sum(len(N[x]&f) for x in f)//2))
    for orientation,(arm,opp,low) in enumerate(((u,v,p),(v,u,p[::-1]))):
        for j in range(1,len(arm)-3):
            for L in range(3,min(8,len(arm)-1-j)+1):
                s=arm[j:j+L+1];near=set(s)|set.union(*(N[x] for x in s));conf=[t for t,x in enumerate(low) if x in near]
                span=max(conf)-min(conf)+1 if conf else 0
                out.append((span,len(conf),i,orientation,j,L,conf))
(D/'seeds.dat').write_text('\n'.join(seeds)+'\n');(D/'trims.tsv').write_text('\n'.join('\t'.join(map(str,r)) for r in trim)+'\n')
print('existing arm subpaths',len(out),'best contiguous lower blocker spans',sorted(out)[:14])
