from pathlib import Path
from collections import Counter
from random import Random
import json,subprocess,sys
D=Path(__file__).resolve().parent
def load():
    raw=(D/'sections.pts').read_text().splitlines()
    c=[list(map(int,l.split())) for l in (D/'canonical_charts.tsv').open()]
    return raw,c
def audit(raw,c):
    rep={};ranks=Counter()
    for line,row in zip(raw,c):
        r,m,b,n,k,x,*axes=row;p=list(map(int,line.split()));assert p[:4]==row[:4]
        inv=[x]
        for a in axes:inv+=[w^a for w in inv]
        assert len(set(inv))==len(inv);ranks[len(axes)]+=1
        lookup={val:i for i,val in enumerate(inv)};canon=sum(1<<lookup[y] for y in p[4:]);assert canon==rep.setdefault(k,canon)
    return dict(total=len(c),classes=len(rep),affine_ranks=dict(ranks))
def known(c):
    idx={(r,m,b):k for r,m,b,n,k,*more in c};known=set()
    for file in ('dense1.log','dense_strata.log','dense_alias.log'):
        path=D/file
        if not path.exists():continue
        for line in path.open():
            v=line.split()
            if len(v)>4 and v[4]=='CLOSED':known.add(idx[tuple(map(int,v[:3]))])
    return known
def main():
    raw,c=load()
    if '--solve' not in sys.argv:print(json.dumps(audit(raw,c)));return
    seen=known(c);pool={k:j for j,(r,m,b,n,k,*more) in enumerate(c) if 194<=n<=198 and k not in seen}
    ids=sorted(pool,reverse=True)
    for i,k in enumerate(ids):
        if i%10==0:seen.update(known(c))
        if k in seen:continue
        out=subprocess.run([str(D/'dense_check'),'1','8','1'],input=raw[pool[k]]+'\n',text=True,capture_output=True,check=True)
        print(out.stdout.strip(),flush=True)
        if 'FOUND' in out.stdout:break
if __name__=='__main__':main()
