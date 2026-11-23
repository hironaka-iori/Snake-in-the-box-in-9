import collections,gzip,json
from pathlib import Path
d=Path(__file__).resolve().parent
def norm(p):
    ds=[(a^b).bit_length() for a,b in zip(p,p[1:])]
    def label(t):
        m={};return tuple(m.setdefault(x,len(m)) for x in t)
    return min(label(ds),label(reversed(ds)))
def verify(p):
    assert len(p)==len(set(p)) and all(0<=x<512 for x in p)
    assert all(((x^y).bit_count()==1)==(j==i+1) for j,y in enumerate(p) for i,x in enumerate(p[:j]))
def possible(e):
    if len(e)!=len(set(e)):return False
    deg=collections.Counter(x^(1<<i) for x in e for i in range(9))
    for a,b in zip(e,e[1:]):
        if (a^b).bit_count()!=2:return False
        if not any(deg[a^(1<<i)]==2 for i in range(9) if ((a^b)>>i)&1):return False
    return True
allseeds={}
for l in (d/'inputs.txt').open():
    t,id,n,*p=map(int,l.split());assert len(p)==n;allseeds[id]=p
    if t==1:verify(p)
    else:
        assert all((a^b).bit_count()==1 for a,b in zip(p,p[1:])) and len(set(p))==193
        assert sum((a^b).bit_count()==1 for j,b in enumerate(p) for a in p[:max(0,j-1)])==2
known=set()
with gzip.open(d.parent/'q9_port_followup_public191.txt.gz','rt') as f:
    for l in f:
        p=list(map(int,l.split()));verify(p);known.add(norm(p))
rows={}
for f in sorted(d.glob('*.log')):
    classes=set();outside=set();rc=0;positive=0;rep=None;deltas=[];stat=[];hard={}
    for l in f.open():
        t=l.split()
        if t[0]=='COUNT':stat=list(map(int,t[2:]));continue
        if t[0]=='C':
            id,flip,k,i,x,j,y=map(int,t[1:]);e=allseeds[id][flip::2];assert i<len(e)//2<j
            for h,v in [(i,x),(j,y)]:
                ee=e.copy();ee[h]=v
                assert len(ee)==len(set(ee)) and all((a^b).bit_count()==2 for a,b in zip(ee,ee[1:])) and not possible(ee)
            hard[id,flip,k]=(x,y);positive+=1
        if t[0]!='W':continue
        id,flip,n,k,*p=map(int,t[1:]);verify(p);assert len(p)==n+1
        rc+=1;word=norm(p);classes.add(word)
        if n==191 and word not in known:outside.add(word)
        original=allseeds[id][flip::2];col=original[0].bit_count()%2
        es={v for v in p if v.bit_count()%2==col}
        if f.stem=='hardcontrol':
            assert set(hard[id,flip,k]).isdisjoint(es)
        elif f.stem!='controls':
            mid=len(original)//2
            losses=[len(set(original[:mid])-es),len(set(original[mid:])-es)]
            assert min(losses)>0;deltas.append(losses)
        if rep is None:rep=p
    assert stat,(f.name,'no finish')
    assert rc==stat[-1],(f.name,rc,stat)
    rows[f.stem]=dict(layouts=stat[0],viable_core=stat[1],nodes=stat[2],capped=stat[3],witnesses=rc,classes=len(classes),outside_public191=len(outside),double_poison=positive)
    if deltas:rows[f.stem]['loss_ranges']=[[min(x[i] for x in deltas),max(x[i] for x in deltas)] for i in [0,1]]
    if rep and f.stem=='archive191':(d/'best191.json').write_text(json.dumps(rep)+'\n')
names=['seven','archive','sevenodd','archiveodd','warp7even','warp7odd','warp191even','warp191odd','perm7e','perm7o','perm191e','perm191o']
summary={key:sum(rows[n][key] for n in names) for key in ['layouts','viable_core','nodes','capped','witnesses']}
exact_names=["exact7e","exact7o","exact191e","exact191o"]
exact={key:sum(rows[n][key] for n in exact_names) for key in ["layouts","viable_core","nodes","capped","witnesses"]}
for name,n,repeats,tips in [("exact7e",97,7,0),("exact7o",97,7,2),("exact191e",96,104,0),("exact191o",96,104,2)]:
    mid=n//2
    assert rows[name]["layouts"]==repeats*sum((mid-i+1)*(n-mid-j)*(i+j+98-tips//2-n) for i in (1,2) for j in (1,2))
print(json.dumps({"small_domain":exact,'target192':summary,'archive_classes':len(known),'batches':rows},indent=2))
