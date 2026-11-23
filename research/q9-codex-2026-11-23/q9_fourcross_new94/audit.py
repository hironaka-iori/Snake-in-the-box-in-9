from pathlib import Path
from collections import Counter
from itertools import groupby
import json
D=Path(__file__).resolve().parent
def induced(p,dim):
    assert len(set(p))==len(p) and all(0<=v<2**dim for v in p)
    for j,v in enumerate(p):
        for i,u in enumerate(p[:j]):assert ((v^u).bit_count()==1)==(i+1==j)
def overlap(p,q):
    seen={x:i for i,x in enumerate(q)};best=0
    for walk in (p,p[::-1]):
        for j,x in enumerate(walk):
            if x not in seen:continue
            t=0;k=seen[x]
            while j+t<len(walk) and k+t<len(q) and walk[j+t]==q[k+t]:t+=1
            best=max(best,t-1)
    return best
old=[]
for row in (D/'seeds.dat').read_text().splitlines():
    i,n,*v=map(int,row.split());p=v[:n];v=v[n:];k=v[0];a=v[1:k+1];b=v[k+2:];full=[x+256 for x in a[::-1]]+p+[x+256 for x in b];induced(full,9);assert len(full)==190;old.append(p)
raw=[];N=[{v^1<<j for j in range(8)} for v in range(256)]
for i,org in enumerate(old):
    for L in (92,93):
        for j in range(len(org)-L):
            p=org[j:j+L+1];f=set(range(256))-set(p)-set.union(*(N[v] for v in p));raw.append([i,L,j,len(f),sum(len(N[v]&f) for v in f)//2])
assert sorted(raw)==sorted([list(map(int,x.split())) for x in (D/'trims.tsv').read_text().splitlines()])
stats={};best={};forest={}
for file in ['freer92.dat','spliced.dat','splice93_0.dat','splice93_1.dat']:
    seen=set();banks=[]
    for line in (D/file).read_text().splitlines():
        seed,rev,lo,hi,n,*v=map(int,line.split());p=v[:n];s=v[n+1:];induced(p,8);induced(s,8);assert all((a^b).bit_count()>1 for a in p for b in s);assert overlap(p,old[seed])>=hi-lo;seen.add((tuple(sorted(p)),tuple(sorted(s))));banks.append((seed,p,s))
    forest[file]=banks;stats[file]=dict(rows=len(banks),distinct_occupied_geometries=len(seen))
report={}
for file in sorted(D.glob('*.paths')):
    rows=[]
    for line in file.read_text().splitlines():
        v=list(map(int,line.split()));e=v[0];p=v[-e-1:];meta=v[:-e-1];induced(p,9);groups=[list(g) for k,g in groupby(p,lambda x:x>=256)];assert p[0]>=256 and p[-1]>=256 and len(groups)==5
        major,second=sorted([groups[1],groups[3]],key=len,reverse=True)
        if file.name.startswith(('target','short','deeper','control')):seed=meta[1]
        elif file.name.startswith('joint'):seed=meta[2]
        elif file.name.startswith(('free184','discover','p192','connected')):seed=1
        elif file.name.startswith(('conn93a','linked0','sp0')):seed=0
        elif file.name.startswith('conn93b'):seed=1
        else:seed=meta[2]
        L=len(major)-1;K=len(second)-1
        if not file.name.startswith('control'):assert L in (92,93) and 3<=K<=8
        rows.append((e,seed,L,K,overlap(major,old[seed])))
        kk=(seed,L)
        if kk not in best or (e,rows[-1][-1])>best[kk][:2]:best[kk]=(e,rows[-1][-1],K,file.name)
    if rows:report[file.name]=dict(rows=len(rows),best=max(z[0] for z in rows),best_overlaps=sorted({z[-1] for z in rows if z[0]==max(x[0] for x in rows)}))
witness=json.loads((D/'witness184.json').read_text());p=witness['path'];induced(p,9);assert witness['edges']+1==len(p)==185
w=''.join(str((u^v).bit_length()-1) for u,v in zip(p,p[1:]));assert w==witness['transitions'] and [j for j,c in enumerate(w) if c=='8']==witness['crossing_step_indices']
g=[list(a) for _,a in groupby(p,lambda x:x>=256)];assert [len(a)-1 for a in g]==witness['component_edge_counts']
main,short=sorted([g[1],g[3]],key=len,reverse=True);source,ref,rs=forest['freer92.dat'][witness['lower_forest_row']];assert set(main)==set(ref) and set(short)==set(rs) and overlap(main,old[source])==63
records={}
for file in ('retry192','sp0target','joint192','all93','joint188','joint186'):
    rec=[json.loads(l) for l in (D/(file+'.jsonl')).read_text().splitlines()];records[file]=dict(Counter(str(r.get('answer',r.get('outcome'))) for r in rec))
print(json.dumps(dict(witness184_verified=True,search_outcomes=records,original_seeds=2,trim_check=raw,forest=stats,verified_paths=report,best={str(k):v for k,v in best.items()}),indent=1))
