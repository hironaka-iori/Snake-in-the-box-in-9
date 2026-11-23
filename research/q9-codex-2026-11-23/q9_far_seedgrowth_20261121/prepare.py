from collections import defaultdict,Counter
from functools import lru_cache
from pathlib import Path
import json,random,sys
D=Path(__file__).resolve().parent;R=D.parent
NB=[{v^(1<<j) for j in range(9)} for v in range(512)]
def paircheck(p):
    assert len(set(p))==len(p) and all(((a^p[j]).bit_count()==1)==(j==i+1) for i,a in enumerate(p) for j in range(i+1,len(p)))
def read():
    bank={};group={};groups=defaultdict(list)
    for l in (R/'q8_registered_donor_clusters.txt').open():
        g,i,*p=map(int,l.split());bank[i]=p;group[i]=g;groups[g].append(i)
    return bank,group,groups
bank,group,groups=read();rng=random.Random(482113)
@lru_cache(maxsize=8192)
def img(i,perm):
    return [sum(1<<int(perm[d]) for d in range(8) if v>>d&1) for v in bank[i]]
@lru_cache(maxsize=8192)
def mapped(i,pm,t):return [256+(v^t) for v in img(i,pm)]
def bitpath(p):return sum(1<<v for v in p)
def rootloss(p,h):
    s=set(p)
    return len(set().union(*(NB[v] for v in p[1:-1]))&h-s)
def emit(dst,ln,e,h,root,nodes,tag):
    print(ln,e,nodes,tag,len(h),*sorted(h),len(root),*root,file=dst)
def candidates(a,b):
    # Walk toward one shared column in the lower facet and away in the upper
    # facet. Shorten the lower arm whenever another vertical contact enters.
    lower={x:i for i,x in enumerate(a)}
    for j,v in enumerate(b):
        x=v-256
        if x not in lower:continue
        pos=lower[x]
        for left in (a[:pos+1][::-1],a[pos:]):
            idx={v:i for i,v in enumerate(left)}
            for right in (b[j::-1],b[j:]):
                keep=len(left)
                for k in range(1,len(right)+1):
                    y=right[k]-256 if k<len(right) else None
                    if y is None or y in idx and idx[y]<keep:
                        if keep+k>=80: yield left[:keep][::-1]+right[:k]
                        if y is not None:keep=idx[y]
def run():
    rows=[]; banks=defaultdict(list)
    for ln,l in enumerate((R/'q8_near_host_placements.log').open(),1):
        if not l.startswith('HOST '):continue
        _,a,b,t,k,pm=l.split();a,b,t,k=map(int,[a,b,t,k]);r=(ln,a,b,t,k,pm)
        if k<=5:rows.append(r);banks[k].append(r)
    selected=[]
    for k in (2,3,4,5):selected+=rng.sample(banks[k],min(850,len(banks[k])))
    rng.shuffle(selected)
    traces=[d['vertices'] for d in json.load(open(R/'q9_five_host_external_blocks_20261121/nine_witnesses.json'))]
    traces += [d['path'] for d in json.load(open(R/'q9_five_host_external_blocks_20261121/seeds.json'))]
    traces += [json.loads((R/'q9_nearhost_free_20261121/real_control.jsonl').read_text().splitlines()[-1])['witness']]
    traces=list({tuple(q):q for q in traces}.values())
    for q in traces:paircheck(q)
    masks=[bitpath(q) for q in traces]; exact=[];control_records=[];known=set();stats=Counter();joint=Counter();initial=Counter()
    with (D/'knownroots.dat').open('w') as dest,(D/'controls.dat').open('w') as ctrl:
        for ln,a,b,t,k,pm in rows:
            h=set(bank[a]+mapped(b,pm,t));hm=bitpath(h)
            for idx,m in enumerate(masks):
                count=(m&~hm).bit_count()
                if not 6<=count<=15:continue
                initial[count]+=1;q=traces[idx]
                if len(control_records)<120 and count not in control_records:
                    root=q[7:-8];emit(ctrl,ln,count,h,root,90000,idx);control_records.append(count)
                if (count,idx) not in known or rng.randrange(25)==0:
                    known.add((count,idx))
                    if len(exact)<3000:
                        off=rng.randrange(3,36);r=rng.randrange(3,36);p=q[off:-r]
                        e=min(15,max(count,rng.choice((6,9,12,15))))
                        emit(dest,ln,e,h,p,15000,idx);exact.append(ln)
    with (D/'borrowed.dat').open('w') as out:
        for ln,a,b,t,k,pm in selected:
            h=set(bank[a]+mapped(b,pm,t));assert len(h)==len(bank[a])+len(bank[b])
            opts=set()
            for trial in range(10):
                aa=rng.choice(groups[group[a]]);bb=rng.choice(groups[group[b]])
                if aa==a and bb==b:continue
                for q in candidates(bank[aa],mapped(bb,pm,t)):
                    if len(q)>190:q=q[rng.randrange(0,8):len(q)-rng.randrange(1,8)]
                    if not 80<=len(q)<=190:continue
                    outside=len(set(q)-h)
                    if not 2<=outside<=15:continue
                    key=(outside,tuple(q))
                    opts.add(key)
            options=list(opts);rng.shuffle(options);options.sort(key=lambda x:-len(x[1]))
            kept=0
            for outside,p in options[:32]:
                e=rng.choice([e for e in (6,9,12,15) if e>=outside]); lost=rootloss(p,h)
                if lost>len(h)+e-193:continue
                emit(out,ln,e,h,p,16000,100+kept);stats[e]+=1;joint[outside]+=1;kept+=1
                if kept==3:break
    print(json.dumps(dict(sampled_low_overlap=len(selected),borrowed_counts=stats,root_outsiders=joint,known_root_cases=len(exact),known_geometries=initial,positive_samples=len(control_records)),indent=2))
if __name__=='__main__':run()
