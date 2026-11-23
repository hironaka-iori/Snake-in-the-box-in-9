from pathlib import Path
from collections import Counter,defaultdict
from itertools import combinations
import json,re,sys
D=Path(__file__).resolve().parent;R=D.parent
def walk(w):
    r=[0]
    for a in w:r.append(r[-1]^1<<int(a))
    return r
def key(w):
    a=list(dict.fromkeys(w));b=list(dict.fromkeys(w[::-1]))
    return min(''.join(str(a.index(k)) for k in w),''.join(str(b.index(k)) for k in w[::-1]))
def true(p):
    return len(p)==len(set(p)) and all(0<=x<512 for x in p) and all(((a^b).bit_count()==1)==(j-i==1) for i,a in enumerate(p) for j,b in enumerate(p[i+1:],i+1))
cs=list(map(json.loads,(D/'cases.jsonl').read_text().splitlines()))
root=(R/'q8_single_cross_complete_arms.txt').read_text().split()
bank=(R/'q8_catalogue_96_98.words').read_text().split()
WS={key(w) for w in root}
for w in bank:
    for start in range(4):
        for stop in range(4-start):
            s=w[start:len(w)-stop]
            if len(s)>=93:WS.add(key(s))
pairs=set()
for w in WS:
    p=walk(w)
    forbidden=0
    for x in p:
        forbidden|=1<<x
        for j in range(8):forbidden|=1<<(x^1<<j)
    free=set(range(256))-{x for x in range(256) if forbidden>>x&1}
    for a,b in combinations(sorted(free),2):
        if (a^b).bit_count()==1:pairs.add((w,a,b))
got={(c['w'],*c['edge']) for c in cs}
assert len(cs)==len(got) and got==pairs
for c in cs:
    p=c['lo'];a,b=c['edge'];assert p==walk(c['w']) and true(p)
    assert all((z^x).bit_count()>=2 for z in (a,b) for x in p)
    quad=(a,b,b+256,a+256)
    assert all((quad[k]^quad[(k+1)%4]).bit_count()==1 for k in range(4)) and (quad[0]^quad[2]).bit_count()==(quad[1]^quad[3]).bit_count()==2
def validate(i,p):
    assert true(p)
    c=cs[i];a,b=c['edge'];lower=set(c['lo'])|{a,b};assert {x for x in p if x<256}==lower
    ports={min(x,y) for x,y in zip(p,p[1:]) if x^y==256}
    assert len(ports&{a,b})==1 and ports-{a,b}<={c['lo'][0],c['lo'][-1]}
    k=len(ports);assert k in {2,3} and sum(v<256 for v in (p[0],p[-1]))==4-k
    return k
runs={};overall={};best={}
for file in sorted(D.glob('*.paths')):
    cc=Counter();maxima={}
    for ln in file.read_text().splitlines():
        i,n,*p=map(int,ln.split());assert len(p)==n+1;k=validate(i,p)
        cc[k]+=1;maxima[k]=max(maxima.get(k,0),n)
        if n>overall.get(k,0):
            overall[k]=n;best[k]={'file':file.name,'case':i,'vertices':p,'edges':n}
    runs[file.stem]=dict(counts=cc,best=maxima)
sats={}
for nm in ('sat192','local_full192','local_scores','extra_scores','extra192','positive'):
    cc=Counter()
    for r in map(json.loads,(D/(nm+'.jsonl')).read_text().splitlines()):
        for z in r.get('branches',[r]):
            cc[z['status']]+=1
            if z.get('vertices'):
                p=z['vertices'];assert validate(r['case'],p)==r['cross'] and len(p)>=1+r.get('goal',191)
    sats[nm]=cc
old=[]
for r in map(json.loads,(D/'archive_controls.jsonl').read_text().splitlines()):
    p=r['vertices'];k=validate(r['case'],p);assert k==2 and len(p)==192
    w=''.join(str((a^b).bit_length()-1) for a,b in zip(p,p[1:]));archive=(R/'q9_gap_generations/prior191.words').read_text().split()
    assert key(w)==key(archive[r['row']]);old.append((r['case'],r['row']))
ans=dict(catalogue_classes=len(WS),geometry=len(cs),source_lengths={str(k):v for k,v in Counter((c['source'][0],len(c['w'])) for c in cs).items()},paired_replay=old,best=overall,runs=runs,sat=sats)
(D/'verified.json').write_text(json.dumps(ans,indent=2)+'\n')
(D/'best.json').write_text(json.dumps(best,separators=(',',':'))+'\n')
print(json.dumps(ans,indent=2))
