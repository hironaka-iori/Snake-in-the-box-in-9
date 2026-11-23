"""Re-embed a walk with prescribed Hamming weight inside each coordinate group at every time."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import argparse,json,random
from pysat.solvers import Solver

def valid(path):
    return len(set(path))==len(path) and all(0<=v<512 for v in path) and all(
        ((x^y).bit_count()==1)==(i+1==j) for (i,x),(j,y) in combinations(enumerate(path),2))

def repair(path,masks,gauge,budget):
    assert sum(masks)==511 and all(not (a&b) for a,b in combinations(masks,2))
    rows=[];groups=[];formula=[];phase=[];uid=0
    def new():
        nonlocal uid
        uid+=1
        return uid
    for mask in masks:
        previous=-1; labels=[]; times=[]; run_weights=[]
        bits=[i for i in range(9) if mask>>i&1]
        all_values=[sum(1<<bits[i] for i in range(len(bits)) if n>>i&1) for n in range(1<<len(bits))]
        for v in path:
            v=(v^gauge)&mask
            if v!=previous:
                weight=v.bit_count();domain={u:new() for u in all_values if u.bit_count()==weight}
                if labels:
                    before=rows[labels[-1]]
                    assert abs(weight-run_weights[-1])==1
                    for u,lit in before.items():
                        formula.append([-lit]+[x for w,x in domain.items() if (u^w).bit_count()==1])
                labels.append(len(rows));run_weights.append(weight);rows.append(domain)
                lits=list(domain.values());formula.append(lits);formula.extend([ -x,-y] for x,y in combinations(lits,2))
                phase.append(domain[v]);previous=v
            times.append(labels[-1])
        groups.append(times)
    # All coordinate permutations inside each group act on the full path.
    for times in groups:formula.append([next(iter(rows[times[0]].values()))])
    rel_cache={}
    def bad(a,b,d):
        if a==b:return True
        if a>b:a,b=b,a
        key=(a,b,d)
        if key in rel_cache:return rel_cache[key]
        bad_pairs=[(x,y) for u,x in rows[a].items() for v,y in rows[b].items() if (u^v).bit_count()==d]
        if not bad_pairs:result=False
        elif len(bad_pairs)==len(rows[a])*len(rows[b]):result=True
        else:
            result=new();formula.extend([-x,-y,result] for x,y in bad_pairs)
        rel_cache[key]=result
        return result
    signatures=[tuple(g[i] for g in groups) for i in range(len(path))]
    weights=[tuple(((v^gauge)&m).bit_count() for m in masks) for v in path]
    buckets={}
    for i,w in enumerate(weights):
        low=[w]
        for d,mask in enumerate(masks):
            for step in (-1,1):
                if 0<=w[d]+step<=mask.bit_count():low.append(w[:d]+(w[d]+step,)+w[d+1:])
        for weight in low:
            for j in buckets.get(weight,[]):
                if j==i-1:continue
                clause=[]
                for a,b,u,v in zip(signatures[i],signatures[j],w,weight):
                    value=bad(a,b,abs(u-v))
                    if value is False:break
                    if value is not True:clause.append(-value)
                else:
                    if not clause:return 'UNSAT',None,0
                    formula.append(clause)
        buckets.setdefault(w,[]).append(i)
    with Solver(name='cadical195',bootstrap_with=formula) as s:
        s.set_phases(phase);s.conf_budget(budget)
        ans=s.solve_limited(); conflicts=s.accum_stats()['conflicts']
        if ans is not True:return ('UNSAT' if ans is False else 'UNKNOWN'),None,conflicts
        model=set(s.get_model())
    vs=[next(v for v,x in domain.items() if x in model) for domain in rows]
    witness=[gauge^sum(vs[i] for i in row) for row in signatures]
    assert valid(witness)
    assert all(((v^gauge)&m).bit_count()==((u^gauge)&m).bit_count() for v,u in zip(path,witness) for m in masks)
    return 'FOUND',witness,conflicts
def main():
    cli=argparse.ArgumentParser();cli.add_argument('shape');cli.add_argument('count',type=int);cli.add_argument('seed',type=int);cli.add_argument('budget',type=int);cli.add_argument('--control',action='store_true');args=cli.parse_args()
    here=Path(__file__).resolve().parent
    if args.control:
        p=list(map(int,(here.parent/'q9_elastic_blocks_20261121/parents191.vertices').read_text().splitlines()[0].split()))
        assert len(p)==192 and valid(p)
        for i in range(1,len(p)-1):
            y=p[i-1]^p[i+1]^p[i];q=p.copy();q[i]=y
            if len(set(q))<len(q) or valid(q):continue
            assert (y^p[i]).bit_count()==2
            m=y^p[i];axes=[j for j in range(9) if not (m>>j&1)]
            masks=[m,sum(1<<a for a in axes[:3]),sum(1<<a for a in axes[3:])]
            gauge=0 if (y&m).bit_count()==1 else m&-m
            status,w,c=repair(q,masks,gauge,args.budget)
            if status=='FOUND':
                print(json.dumps(dict(damaged=q,damaged_index=i,masks=masks,gauge=gauge,witness=w,conflicts=c)));return
        raise ValueError('control failed')
    bank=[list(map(int,s.split())) for s in (here.parent/'q9_onechord_expanded_800.txt').read_text().splitlines()]
    rng=random.Random(args.seed);shape=list(map(int,args.shape));assert sum(shape)==9
    for idx in range(args.count):
        row=rng.randrange(len(bank));axes=list(range(9));rng.shuffle(axes);offset=0;masks=[]
        for n in shape:
            masks.append(sum(1<<j for j in axes[offset:offset+n]));offset+=n
        gauge=rng.randrange(512)
        status,w,c=repair(bank[row],masks,gauge,args.budget)
        print(json.dumps([idx,row,masks,gauge,status,c,w],separators=(',',':')),flush=True)
        if status=='FOUND':break
if __name__=='__main__':main()
