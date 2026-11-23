"""Test time-indexed SAT domains from whole-walk coordinate alignments."""
import argparse
import json
import random
from functools import lru_cache
from pathlib import Path
from search_q9_time_vertex_lists import check, solve_domains

def columns(p):
    return [sum(((v>>i)&1)<<t for t,v in enumerate(p)) for i in range(9)]

def align(parent, dest, destcols):
    src=columns(parent)
    n=len(parent)
    costs=[[(x^y).bit_count() for y in destcols] for x in src]
    # All walks alternate vertex parity. Optimize over parity-preserving alignments.
    parity=(parent[0]^dest[0]).bit_count()%2
    @lru_cache(None)
    def fit(mask,needed):
        i=mask.bit_count()
        if i==9:return (0 if needed==0 else 100000, ())
        best=(100000, ())
        for j,d in enumerate(costs[i]):
            if mask>>j&1:continue
            for f,c in enumerate((d,n-d)):
                rest,assignment=fit(mask|(1<<j),needed^f)
                if c+rest<best[0]:best=(c+rest,((j,f),)+assignment)
        return best
    score,assign=fit(0,parity)
    trans=sum(f<<j for j,f in assign)
    lookup=[trans]
    for j,_ in assign:
        lookup += [v^(1<<j) for v in lookup]
    return score,[lookup[x] for x in parent]

def domains(parents):
    lists=[set(q) for q in zip(*parents)]
    for p in parents:
        for t in range(1,len(p)-1):
            if (p[t-1]^p[t+1]).bit_count()==2:
                lists[t].add(p[t-1]^p[t]^p[t+1])
    return lists

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('source');ap.add_argument('count',type=int);ap.add_argument('salt',type=int)
    a=ap.parse_args();rng=random.Random(a.salt)
    ctrl=json.loads(Path('q9_independent_connectors_damaged_control.json').read_text())
    seed=ctrl['source']; fixed=json.loads(Path('q9_time_vertex_lists_first.jsonl').open().readline())[3]
    donor=[(((v&255)<<1)|(v>>8))^37 for v in fixed]
    cost,aligned=align(donor,seed,columns(seed))
    status,w=solve_domains(seed,domains([seed,aligned]),15000)
    assert status=='FOUND' and check(w)
    print(json.dumps(['control',cost,status,len(w)-1]),flush=True)
    bank=[list(map(int,line.split())) for line in Path(a.source).read_text().splitlines()]
    for run in range(a.count):
        idx=rng.randrange(len(bank));seed=bank[idx];cols=columns(seed)
        roster=rng.sample(range(len(bank)),10)
        candidates=[]
        for k in roster:
            q=bank[k]
            for rev,p in enumerate((q,q[::-1])):
                cost,aligned=align(p,seed,cols)
                if cost:candidates.append((cost,k,rev,aligned))
        best=sorted(candidates)[:5]
        dom=domains([seed]+[row[-1] for row in best])
        status,w=solve_domains(seed,dom,10000)
        print(json.dumps([run,idx,[row[:3] for row in best],status,w]),flush=True)
        if w:
            assert len(w)==193 and check(w)
            break
if __name__=='__main__': main()
