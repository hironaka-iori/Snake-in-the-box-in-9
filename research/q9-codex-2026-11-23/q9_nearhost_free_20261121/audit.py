from collections import Counter
from functools import lru_cache
from pathlib import Path
import sys
import gzip,json
from prepare import D,R,paircheck
FULL=(1<<512)-1;LOW=(1<<256)-1;PAR=sum(1<<v for v in range(512) if v.bit_count()%2)
Z=[sum(1<<v for v in range(512) if not (v>>d&1)) for d in range(9)]
def shift(b,d):
    k=1<<d;z=Z[d];return ((b&z)<<k)|((b&~z)>>k)
def nb(b):
    out=0
    for d in range(9):out|=shift(b,d)
    return out
def bits(vs):return sum(1<<v for v in vs)
bank={}
for l in (R/'q8_registered_donor_clusters.txt').open():
    _,i,*vs=map(int,l.split());paircheck(vs);bank[i]=vs
hosts={}
@lru_cache(maxsize=24000)
def image(b,pm):
    # Use the inverse mapping to reconstruct which source bit supplies each output bit.
    order=[pm.index(str(i)) for i in range(8)]
    return tuple(sum(((x>>j)&1)<<i for i,j in enumerate(order)) for x in bank[b])
left={k:bits(p) for k,p in bank.items()}
for ln,l in enumerate((R/'q8_near_host_placements.log').open(),1):
    if not l.startswith('HOST '):continue
    _,a,b,t,k,pm=l.split();a,b,t,k=map(int,(a,b,t,k))
    upp=bits(x^t for x in image(b,pm));assert (left[a]&upp).bit_count()==k
    hosts[ln]=left[a]|(upp<<256)
assert len(hosts)==106435
NB_MASK=[sum(1<<(v^(1<<j)) for j in range(9)) for v in range(512)]
def checked(line,f,strict):
    host=hosts[line];assert f&~host==0
    one=two=three=0
    for d in range(9):
        im=shift(f,d);three|=two&im;two|=one&im;one|=im
    assert not (three&f)
    crosses=(f&(f>>256)&LOW).bit_count()
    if strict:assert crosses<=1
    if crosses>=2:
        unseen=f
        while unseen:
            group=unseen&-unseen
            while (nxt:=group|(nb(group)&unseen))!=group:group=nxt
            assert group&~two
            unseen^=group
    # Any additional vertex touching a fixed vertex of degree two, or more than
    # two fixed vertices, cannot be on a path that contains the whole anchor.
    allowed=f|(FULL&~three&~nb(f&two))
    p=(allowed&PAR).bit_count();q=allowed.bit_count()-p
    if len_ub(allowed.bit_count(),p,q)<193:return True
    reachable=0;twor=0
    for d in range(9):
        im=shift(allowed,d);twor|=reachable&im;reachable|=im
    if f&~reachable or (f&~twor).bit_count()>2:return True
    # Disjoint groups of unoccupied neighbors of a fixed vertex can contribute
    # at most its remaining degree capacity. Sum disjoint losses by parity.
    options=allowed&~f;support=f&~two;cuts=[]
    while support:
        b=support&-support;support-=b;x=b.bit_length()-1
        choices=NB_MASK[x]&options;loss=choices.bit_count()-(2-int(bool(b&one)))
        if loss>0:cuts.append((loss,choices,x.bit_count()%2))
    used=0
    for loss,choices,side in sorted(cuts,reverse=True):
        if choices&used:continue
        used|=choices
        if side==0:p-=loss
        else:q-=loss
    return len_ub(p+q,p,q)<193
def len_ub(n,p,q):return min(n,2*min(p,q)+1)
def statuses(file,rows):
    data=[json.loads(l) for l in (D/file).open()];ctrl=data[0]['control']
    for key in ('witness','damaged_witness'):paircheck(ctrl[key]);assert len(ctrl[key])>=192
    assert len(data)==rows+2;assert [x['row'] for x in data[1:-1]]==list(range(rows))
    cs=Counter(x['status'] for x in data[1:-1]);assert cs==data[-1]['counts']
    return dict(cs)
summary={};unique=set();linesets=set();fast=Counter()
for name,results in [('cases',['minicard','cadical']),('dispersed',['disp_minicard','disp_cadical'])]:
    rows=[json.loads(l) for l in (D/(name+'.jsonl')).open()]
    for c in rows:
        f=int(c['fixed'],16);ln=c['line']
        assert f.bit_count()==c['anchors'] and hosts[ln]==int(c['host'],16)
        fast[name]+=checked(ln,f,False);unique.add(f);linesets.add(ln)
    summary[name]=dict(placements=len({c['line'] for c in rows}),regions=len(rows),solvers={n:statuses(n+'.jsonl',len(rows)) for n in results if n!='disp_cadical' or '--pending' not in sys.argv})
all_seen=set();cs=Counter()
with gzip.open(D/'allhosts.jsonl.gz','rt') as src:
    for l in src:
        ln,s,st,w=json.loads(l);f=int(s,16)
        assert f.bit_count()==145 and ln not in all_seen;all_seen.add(ln);assert w is None
        fast['allhosts']+=checked(ln,f,True);unique.add(f);linesets.add(ln);cs[st]+=1
assert all_seen==set(hosts) and json.loads((D/'allhosts.log').read_text().splitlines()[-1])['done']==cs
summary['allhosts']=dict(placements=len(all_seen),regions=sum(cs.values()),solvers={'minicard':dict(cs)})
true=json.loads((D/'real_control.jsonl').read_text().splitlines()[-1]);paircheck(true['witness']);src=json.loads((D/'cases.jsonl').read_text().splitlines()[true['row']]);assert set(true['outside_host'])=={v for v in true['witness'] if not hosts[src['line']]>>v&1}
print(json.dumps(dict(all_placements=len(linesets),distinct_fixed_sets=len(unique),batches=summary,independent_degree_and_parity_exclusions=fast,actual_host_control=dict(line=src['line'],a=src['aid'],b=src['bid'],t=src['t'],perm=src['perm'],overlap=src['overlap'],fixed=src['anchors'],edges=len(true['witness'])-1,outside_host=true['outside_host'])),indent=2))
