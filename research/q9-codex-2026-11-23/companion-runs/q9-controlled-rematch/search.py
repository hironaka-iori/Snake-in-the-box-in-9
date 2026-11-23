"""Repair a controlled coordinate permutation in both parity classes of Q9."""
from collections import Counter, defaultdict
from itertools import combinations
import argparse, hashlib, json, sys, time
from pathlib import Path

def pairwise(p, cycle=False):
    assert len(set(p)) == len(p) and all(0 <= x < 512 for x in p)
    assert all(((x^y).bit_count()==1)==(j==i+1 or cycle and i==0 and j==len(p)-1)
               for i,x in enumerate(p) for j,y in enumerate(p) if j>i)

def encode(p):
    def norm(seq):
        m={};return bytes(m.setdefault(x,len(m)) for x in seq)
    w=[a^b for a,b in zip(p,p[1:])]
    return min(norm(w),norm(w[::-1]))

def load_sources(repo):
    seen=set();out=[]
    for j,l in enumerate((repo/'q9_record_single_crossing_191.jsonl').read_text().splitlines()):
        p=[0]
        for d in json.loads(l)['steps']:p.append(p[-1]^(1<<int(d)))
        pairwise(p);key=encode(p)
        if key not in seen: out.append((f'public_{j}',p,False));seen.add(key)
    rec=json.loads((repo/'q9_coil_open_191_witness.json').read_text())
    pairwise(rec['cycle'],True);pairwise(rec['path'])
    return out+[('coil',rec['cycle'],True),('opened_coil',rec['path'],False)]

def permutations(control,kind):
    axes=[i for i in range(9) if i!=control]
    if kind=='swap':yield from combinations(axes,2)
    else:
        for a,b,c in combinations(axes,3):yield (a,b,c);yield (a,c,b)

def moved(x,bits):
    return x ^ sum(((((x >> bits[i-1]) ^ (x >> d))&1)<<d) for i,d in enumerate(bits))

def prepare(sources):
    # Retain candidates based on the full image, before any target search.
    pools=defaultdict(list);total=Counter()
    for name,p,cycle in sources:
        S=set(p);n=len(p)
        for ctl in range(9):
            bit=1<<ctl;low={v:i for i,v in enumerate(p) if not v&bit}
            high=[(v,i) for i,v in enumerate(p) if v&bit]
            original=[(low[v^bit],i) for v,i in high if v^bit in low]
            for kind in ('swap','three'):
                for bits in permutations(ctl,kind):
                    for sign in (0,1):
                        # Conjugate by a translation on the first active axis in one mode.
                        shift=(1<<bits[0]) if sign else 0
                        f=lambda v: moved(v^shift,bits)^shift
                        H=[(f(v),i) for v,i in high]
                        old=set(original);new={(low[v^bit],i) for v,i in H if v^bit in low}
                        loss,add=old-new,new-old
                        total['transforms']+=1
                        if not (1<=len(loss)+len(add)<=20):continue
                        delta=sum(v not in S for v,i in H)
                        if delta<3:continue
                        bad={i for edge in loss|add for i in edge}
                        spec=(name,ctl,kind,bits,sign)
                        pools[(name,kind)].append((len(loss)+len(add),len(bad),-delta,spec,sorted(bad),len(loss),len(add)))
                        total['retained']+=1
    for vals in pools.values():vals.sort()
    return pools,total

def image_case(p,cycle,row,radius):
    _,_,_,(name,ctl,kind,bits,sign),bad,loss,add=row
    mask=1<<ctl;shift=(1<<bits[0]) if sign else 0
    q=[(moved(x^shift,bits)^shift) if x&mask else x for x in p]
    assert len(set(q))==len(p)
    centers=list(bad)
    if not cycle:centers += [0,len(p)-1]
    release={((i+j)%len(p)) for i in centers for j in range(-radius,radius+1) if cycle or 0<=i+j<len(p)}
    fixed={v for i,v in enumerate(q) if i not in release}
    return set(q),fixed

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('repo',type=Path);ap.add_argument('output',type=Path)
    ap.add_argument('--n',type=int,default=5);ap.add_argument('--radius',type=int,default=4)
    ap.add_argument('--budget',type=int,default=2000);ap.add_argument('--target',type=int,default=192)
    ap.add_argument('--strata',type=int,default=0)
    ap.add_argument('--salt',type=int,default=0)
    a=ap.parse_args();sys.path.insert(0,str(a.repo))
    from search_q9_anchored_sets import search
    sources=load_sources(a.repo);byname={nm:(p,c) for nm,p,c in sources}
    pools,counts=prepare(sources)
    print(dict(source_count=len(sources),**counts),flush=True)
    statuses=Counter();seen=set();rows=[]
    for key,values in sorted(pools.items()):
        if a.strata:
            # Include positions throughout the 1..20 defect range, not just closest images.
            values=sorted(values,key=lambda v:hashlib.blake2s(repr((v[3],a.salt)).encode(),digest_size=8).digest())
        done=0
        for row in values:
            p,cycle=byname[key[0]];seed,fixed=image_case(p,cycle,row,a.radius)
            if len(fixed)<70 or len(fixed-set(p))<2 or frozenset(fixed) in seen:continue
            bit=1<<row[3][1]
            if any(not any(bool(v&bit)==c for v in seed-fixed) for c in [False,True]):continue
            seen.add(frozenset(fixed));done+=1
            st,w=search(fixed,seed,a.target,a.budget)
            item=dict(transform=row[3],lost=row[-2],extra=row[-1],radius=a.radius,known_fixed=len(fixed),fixed_novel=len(fixed-set(p)),status=st)
            if w is not None:
                pairwise(w);assert len(w)==a.target+1 and fixed<=set(w)
                item.update(vertices=w,added=len(set(w)-seed),deleted=len(seed-set(w)))
            statuses[st]+=1;rows.append(item)
            if (w and a.target==192) or done>=a.n:break
        if rows and rows[-1].get('vertices') and a.target==192:break
    a.output.write_text(json.dumps(dict(inputs=[n for n,_,_ in sources],parameters={k:str(v) if isinstance(v,Path) else v for k,v in vars(a).items()},generation=counts,status_counts=statuses,results=rows),separators=(',',':'))+'\n')
    print(statuses,flush=True)
if __name__=='__main__':main()
