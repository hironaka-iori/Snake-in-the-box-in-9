"""Recheck an integer facet dual and search branches which still allow a target."""
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import gzip,json,os,sys,subprocess
from concurrent.futures import ProcessPoolExecutor
from io import StringIO
from split_q9_long_donor_ports import path
from verify_q8_free_layer_dual import is_forest
def valid(w):
    return len(w)==len(set(w)) and all(0<=v<512 for v in w) and all(((x^w[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(w) for j in range(i+1,len(w)))

def branch(r,goal=192,cap=350000,pinned=None):
    p=path(r['word']);added=set(r['added']);ports=set(r['ports']);low=set(p)|added
    c=r['cert'];blocks=[tuple(1<<a for a in ax) for ax in c['axes']]
    masks=list(map(sum,blocks));scale=c['scale'];allowed=set(range(256))-(low-ports)
    weights={(m,v,h):y for m,v,h,y in c['weights']};b=c['balance_weight'];fw=c['end_weights']
    deg={v:sum(v^1<<d in low for d in range(8))+int(v in ports) for v in low}
    assert all(1<=i<=2 for i in deg.values())
    full=r['full'];end=[full[h]-sum(z==1 and v.bit_count()%2==h for v,z in deg.items()) for h in (0,1)]
    delta=sum((-1)**v.bit_count() for v in low)-(full[0]-full[1])//2
    assert min(end)>=0 and end==r['ends'] and r['delta']==delta
    groups=[];sigs={};fee=delta*b+sum(x*y for x,y in zip(end,fw))
    for v in sorted(allowed):
        d=[1<<j for j in range(8) if v^1<<j in allowed]
        area=[v]+[v^h for h in d];hc=(1+v.bit_count())%2
        opts=[] if v in ports else [(0,1,0)]
        good=[]
        for k in (0,1,2):
            total=k+int(v in ports)
            if total!=2 and (total!=1 or not end[hc]):continue
            for ix in combinations(range(len(d)),k):
                z=sum(d[i] for i in ix);good.append(z)
                yes=1+sum(2<<i for i in ix)
                score=scale-b*(-1)**v.bit_count()-(fw[hc] if total==1 else 0)+sum(weights.get((m,v,z&m),0) for m in masks)
                opts.append((yes,((1<<len(area))-1)^yes,score))
        assert opts;groups.append(([v+256 for v in area],opts))
        for m in masks:sigs[v,m]={z&m for z in good}
    for steps,m in zip(blocks,masks):
        cells=defaultdict(list)
        for x in sorted(allowed):cells[x&~m].append(x)
        for vs in cells.values():
            req=ports.intersection(vs);opts=[]
            for bits in range(1<<len(vs)):
                pts={v for i,v in enumerate(vs) if bits>>i&1}
                if not req<=pts or not is_forest(pts,steps):continue
                sig=[(x,sum(d for d in steps if x^d in pts)) for x in pts]
                if any(h not in sigs[x,m] for x,h in sig):continue
                score=-sum(weights.get((m,x,h),0) for x,h in sig)
                opts.append((bits,((1<<len(vs))-1)^bits,score))
            assert opts;groups.append(([v+256 for v in vs],opts))
    upper=fee+sum(max(row[2] for row in opts) for _,opts in groups)
    assert upper==r['numerator']
    length=len(low)-1+upper//scale;length-=int(length%2!=full[0]%2)
    assert length==r['bound']
    target=goal+int(goal%2!=full[0]%2)
    if length<target:return 'DUAL',0,None
    domain=sorted(low|{v+256 for v in allowed})
    for v in low:groups.append(([v],[(1,0,scale)]))
    if pinned:
        for v in pinned:groups.append(([v],[(1,0,0)]))
    upper+=len(low)*scale;buf=StringIO();ep=0 if full[0]==2 else 1
    print(0,target+1,ep,scale,fee,upper,len(domain),*domain,len(groups),file=buf)
    for vs,opts in groups:
        opts.sort(key=lambda row:-row[2])
        print(len(vs),*vs,len(opts),file=buf)
        for row in opts:print(*row,file=buf)
    raw=subprocess.check_output([os.environ.get('Q9_SHELL_SOLVER','/private/tmp/q9_shell_minimum20'),str(cap)],input=buf.getvalue(),text=True,env={**os.environ,'Q9_PATH_MINIMUM':'1'}).split()
    state=raw[1];w=list(map(int,raw[3:])) or None
    if w:
        assert valid(w) and len(w)>goal and {v for v in w if v<256}==low and {v for v in low if v+256 in w}==ports
    return state,int(raw[2]),w
def job(args):
    index,r,goal,cap=args
    if 'empty' in r:return [index,'EMPTY',0,None]
    state,steps,w=branch(r,goal,cap);return [index,state,steps,w]
if __name__=='__main__':
    filename,goal,cap,workers=sys.argv[1:5]
    with gzip.open(filename,'rt') as f:rows=list(map(json.loads,f))
    with ProcessPoolExecutor(int(workers)) as pool:
        for r in pool.map(job,[(i,m,int(goal),int(cap)) for i,m in enumerate(rows)],chunksize=1):
            print(json.dumps(r,separators=(',',':')),flush=True)
            if r[-1]:break
