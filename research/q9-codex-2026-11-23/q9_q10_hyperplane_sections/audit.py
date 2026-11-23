from pathlib import Path
from collections import Counter
from random import Random
from itertools import combinations
import json,subprocess
D=Path(__file__).resolve().parent;R=D.parent
def physical(co,basis):
    x=0
    for i,g in enumerate(basis):
        if co>>i&1:x^=g
    return x
def check(path,dim):
    assert len(path)==len(set(path)) and all(0<=x<1<<dim for x in path)
    for i,j in combinations(range(len(path)),2):assert ((path[i]^path[j]).bit_count()==1)==(j==i+1)
def decode(v):
    j=v.index('BASIS');k=v.index('PATH');bs=list(map(int,v[j+1:k]));p=list(map(int,v[k+1:]));assert len(bs)==9
    assert len({physical(c,bs) for c in range(512)})==512;check(p,9)
    return {physical(c,bs) for c in p},len(p)-1
def recover_chart(y,m,b):
    v=(m&-m).bit_length()-1;x=(y%2**v)+((y//2**v)<<(v+1));return x^(((x&m).bit_count()%2^b)<<v)
def positives():
    src=[list(map(int,line.split()))[1:] for line in (R/'q9_three_seam_folds/q10_12.txt').open()]
    planted=json.loads((D/'positive.json').read_text());matched=0;lengths=[]
    for row,line in zip(planted,(D/'positive.log').open()):
        check(row['mother'],10);ss={x for x in row['mother'] if (x&row['mask']).bit_count()%2==row['side']};raw=[y for y in range(512) if recover_chart(y,row['mask'],row['side']) in ss]
        comp={physical(c,row['axis_chart']) for c in raw};assert comp==set(row['mandatory']);out,n=decode(line.split());assert n==191 and comp<=out;lengths.append(len(row['mother'])-1);matched+=1
    assert matched==16
    cov=Counter()
    for l in (D/'real_controls.log').open():
        v=l.split()
        if v[4]!='FOUND':continue
        r,m,b=map(int,v[:3]);out,n=decode(v)
        U={x for x in src[r] if (x&m).bit_count()%2==b};assert U<={recover_chart(y,m,b) for y in out};cov[n]+=1
    return dict(planted=matched,planted_mother_edges=[min(lengths),max(lengths)],real_379_controls=dict(cov))
def dense_controls():
    rng=Random(119367);plant=json.loads((D/'positive.json').read_text())
    count=Counter()
    for d in (1,2):
        for row in plant[:4]:
            fix=set(row['mandatory']);noise=set(rng.sample(sorted(set(range(512))-fix),d));data=sorted(fix|noise)
            line=' '.join(map(str,[row['source'],row['mask'],row['side'],len(data),*data]))+'\n'
            p=subprocess.run([str(D/'dense_check'),str(d),'8','1','191'],input=line,text=True,capture_output=True,check=True)
            v=p.stdout.splitlines()[0].split();assert v[0]=='FOUND';u,b=map(int,v[v.index('REMOVED')+1:v.index('BASIS')]);removed={x for x in (u,b) if x>=0};out,n=decode(v);assert len(removed)==d and set(data)-removed<=out and n==191;count[d]+=1
    return dict(count)
def direct():
    rows=[list(map(int,l.split())) for l in (D/'sections.pts').open()];rng=Random(133576);direct=[]
    for i in [0,1,2,7,8,9,10,11]:
        direct+=rng.sample([row for row in rows if row[0]==i and (row[1]==1023 or row[3] in (192,193,196,197))],2)
    raw=Counter()
    for row in direct:
        r,m,b,n,*s=row;target=next(t for t in (192,195,196) if n<=t+1);cmd=[str(R/'q9_change_basis/focus'),str(target),'3000000','0','grow']
        p=subprocess.run(cmd,input='points '+' '.join(map(str,s))+'\n',text=True,capture_output=True,check=True)
        assert 'UNKNOWN' not in p.stdout and 'FOUND' not in p.stdout
        raw[(target,n)]+=1
    picked=rng.sample([row for row in rows if row[3]==194],3)
    tests=[]
    for row in picked:
        s=row[4:];tests.extend([s[:i]+s[i+1:] for i in range(len(s))])
    some=[list(map(int,s.split())) for s in (D/'dense_two.in').open() if int(s.split(maxsplit=4)[3])==195]
    for row in some:
        a=row[4:];pairs=rng.sample(list(combinations(range(len(a)),2)),64);tests.extend([[x for k,x in enumerate(a) if k not in (i,j)] for i,j in pairs])
    p=subprocess.run([str(R/'q9_basis_independent/exhaustive'),'0'],input=''.join(' '.join(map(str,s))+'\n' for s in tests),text=True,capture_output=True,check=True)
    assert len(tests)==len(p.stdout.splitlines()) and all(r.split()[2]=='CLOSED' for r in p.stdout.splitlines())
    return dict(independent_parity_sweep=len(direct),independent_all_basis_single_deletions=sum(row[3] for row in picked),independent_all_basis_double_deletions=64*len(some),tested_slice_ids=[r[:3] for r in picked])
def census():
    src=[list(map(int,line.split()))[1:] for line in (R/'q9_three_seam_folds/q10_12.txt').open()]
    for p in src:check(p,10)
    sets=[set(r) for r in src];count=0
    for line in (D/'sections.pts').open():
        r,m,b,n,*s=map(int,line.split());assert n==len(s)==len(set(s))
        assert len(s)==sum((x&m).bit_count()%2==b for x in src[r]) and all(recover_chart(y,m,b) in sets[r] for y in s)
        count+=1
    return count
if __name__=='__main__':print(json.dumps(dict(census_independent=census(),controls=positives(),dense_controls=dense_controls(),negative_cross_check=direct()),indent=2))
