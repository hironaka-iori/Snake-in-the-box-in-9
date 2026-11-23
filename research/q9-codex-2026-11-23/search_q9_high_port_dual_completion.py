"""Check a free Q8 partner with fixed crossing ports and count-conditioned integer factors."""
import argparse
from collections import Counter
from itertools import combinations
from io import StringIO
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import time
from certify_q9_intact_q8_facet import build
from verify_q9_intact98_all_crossings import integer_bound

def geometry(low):
    adj={v:{v^(1<<d) for d in range(8)}&low for v in low}
    assert max(map(len,adj.values()))<=2
    remain=set(low);components=[]
    while remain:
        q=[remain.pop()]
        for x in q:
            add=remain&adj[x];q.extend(add);remain-=add
        assert sum(len(adj[x]) for x in q)==2*(len(q)-1)
        components.append(set(q))
    return {v for v,n in adj.items() if not n},{v for v,n in adj.items() if len(n)==1},components

def cases(low,goal):
    iso,tips,components=geometry(low)
    fulls=((2,0),(0,2)) if goal%2==0 else ((1,1),)
    for k in range(3-len(iso)):
        for leftover in combinations(sorted(tips),k):
            leaf=iso|set(leftover);ports=iso|(tips-set(leftover))
            if not all(c&ports for c in components):continue
            for full in fulls:
                ends=tuple(full[h]-sum(v.bit_count()%2==h for v in leaf) for h in (0,1))
                if min(ends)>=0:yield tuple(sorted(ports)),full,ends

def encode(r):
    return json.dumps(r,separators=(',',':'))

def verify(p,low,ports,full,goal):
    assert len(set(p))==len(p)==goal+1 and all(0<=v<512 for v in p)
    assert all(((v^u).bit_count()==1)==(j==i+1) for i,v in enumerate(p) for j,u in enumerate(p) if j>i)
    assert set(v for v in p if v<256)==low
    assert set(v for v in low if v+256 in p)==set(ports)
    assert tuple(sum(v.bit_count()%2==h for v in (p[0],p[-1])) for h in (0,1))==full

def run(low,branch,goal,binary,cap,count,certfile):
    ports,full,ends=branch
    delta=sum((-1)**v.bit_count() for v in low)-(full[0]-full[1])//2
    axes=list(combinations(range(8),3));random.Random(403215).shuffle(axes);axes=axes[:count]
    x=build([0],ports,low,ends,delta,axes)
    record=dict(ports=ports,full=full,ends=ends,delta=delta,goal=goal,cap=cap)
    if x is None:return dict(record,status='EMPTY'),None
    const,scale,groups,c=x
    num=const+sum(opts[0][2] for _,opts in groups)
    assert num==integer_bound(c,low,set(ports),ends,delta)
    bound=len(low)-1+num//scale;bound-=int(bound%2!=goal%2)
    rec=dict(record,upper=bound,numerator=num)
    cert=dict(rec,low=sorted(low),cert=c)
    if bound<goal:return dict(rec,status='DUAL'),cert
    domain=set(low)|{v+256 for v in set(range(256))-(low-set(ports))}
    buf=StringIO();state=0 if full[0]==2 else 1
    print(0,goal+1,state,scale,const,num+len(low)*scale,len(domain),*sorted(domain),len(groups)+len(low),file=buf)
    for v in sorted(low):print(1,v,1,1,0,scale,file=buf)
    for vs,opts in groups:
        print(len(vs),*(v+256 for v in vs),len(opts),file=buf)
        for on,off,l in opts:print(on,off,l,file=buf)
    env=os.environ.copy();env.pop('Q9_PATH_MINIMUM',None);env.pop('Q9_AVOID_SHAPES',None)
    a=subprocess.check_output([binary,str(cap)],input=buf.getvalue(),text=True,env=env).split()
    p=list(map(int,a[3:]));assert not p or a[1]=='FOUND'
    if p:verify(p,low,ports,full,goal)
    return dict(rec,status=a[1],nodes=int(a[2]),witness=p or None),cert

def main():
    ap=argparse.ArgumentParser();ap.add_argument('bank');ap.add_argument('binary');ap.add_argument('certificates')
    ap.add_argument('--seconds',type=float,default=210);ap.add_argument('--cap',type=int,default=30000)
    ap.add_argument('--faces',type=int,default=6)
    ap.add_argument('--smallest-first',action='store_true')
    ap.add_argument('--already',type=Path)
    a=ap.parse_args()
    processed=set()
    if a.already:
        for l in a.already.read_text().splitlines():
            r=json.loads(l);processed.add((r['index'],tuple(r['ports']),tuple(r['full'])))
    logs=[[json.loads(l) for l in open(f)] for f in ('q9_port_highdim_free_face.jsonl','q9_port_highdim_exact192.jsonl')]
    labels=[{r[0]:r[-2] for r in log[1:]} for log in logs]
    assert labels[0].keys()==labels[1].keys()
    left=[i for i in labels[0] if all(l[i]=='UNKNOWN' for l in labels)]
    assert len(left)==290
    rows=Path(a.bank).read_text().splitlines()
    control=logs[0][0][-1];low={v for v in control if v<256};ports=tuple(sorted(v for v in low if v+256 in control))
    full=tuple(sum(v.bit_count()%2==h for v in (control[0],control[-1])) for h in (0,1))
    matches=[b for b in cases(low,len(control)-1) if (b[0],b[1])==(ports,full)];assert len(matches)==1
    targets=[]
    for i in left:
        g=set(map(int,rows[i].split()[1:]));assert len(g)==len(rows[i].split())-1
        iso,tips,_=geometry(g);bs=list(cases(g,192))
        for j,b in enumerate(bs):
            # Each 2-isolate donor has at most one branch. Then test branches with every tip crossing.
            rank=(0 if len(bs)<=2 else 1,0 if set(b[0])==iso|tips else 1, len(bs),-len(g), j,i)
            if a.smallest_first:rank=(len(bs),j,i)
            if (i,b[0],b[1]) not in processed:targets.append((rank,i,g,b,len(bs)))
    start=time.monotonic();import gzip
    with gzip.open(a.certificates,'wt') as certs:
        def process(i,g,b,n,goal,budget):
            r,c=run(g,b,goal,a.binary,budget,a.faces,certs);r.update(index=i,size=len(g),branch_count=n)
            if c:
                c['index']=i;certs.write(encode(c)+'\n');certs.flush()
            print(encode(r),flush=True)
            return r['status']
        z=process('control',low,matches[0],0,len(control)-1,max(240000,a.cap))
        if z!='FOUND':raise SystemExit('positive control not reconstructed')
        for _,i,g,b,n in sorted(targets,key=lambda job:job[0]):
            if time.monotonic()-start>a.seconds:break
            if process(i,g,b,n,192,a.cap)=='FOUND':break
if __name__=='__main__':main()
