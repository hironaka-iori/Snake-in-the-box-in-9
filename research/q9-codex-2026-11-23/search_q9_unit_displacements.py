"""Try to remove chords by translating each position by one independently chosen unit vector."""
import argparse
import json
import random
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from pysat.solvers import Cadical195

def valid(path):
    return (len(set(path)) == len(path) and all(0 <= v < 512 for v in path)
            and all(((u ^ path[j]).bit_count() == 1) == (j == i+1)
                    for i,u in enumerate(path) for j in range(i+1,len(path))))

@lru_cache(maxsize=None)
def incompatible(delta, consecutive, axes):
    pairs = []
    for i,a in enumerate(axes):
        for j,b in enumerate(axes):
            distance = (delta ^ (1<<a) ^ (1<<b)).bit_count()
            if (distance != 1 if consecutive else distance <= 1):
                pairs.append((i,j))
    return pairs

def solve(path, axes, budget):
    size = len(axes)
    with Cadical195() as sat:
        for i in range(len(path)):
            choices = list(range(1+i*size, 1+(i+1)*size))
            sat.add_clause(choices)
            for a,b in combinations(choices,2):
                sat.add_clause([-a,-b])
        for i,v in enumerate(path):
            for j in range(i+1,len(path)):
                delta = v ^ path[j]
                if j > i+1 and delta.bit_count() > 3:
                    continue
                for a,b in incompatible(delta,j==i+1,axes):
                    sat.add_clause([-(1+i*size+a),-(1+j*size+b)])
        sat.conf_budget(budget)
        answer = sat.solve_limited()
        if answer is not True:
            return ("UNSAT" if answer is False else "UNKNOWN"),None
        model=set(sat.get_model())
        walk=[v ^ (1<<next(a for k,a in enumerate(axes) if 1+i*size+k in model))
              for i,v in enumerate(path)]
        assert valid(walk)
        return "FOUND",walk

def main():
    cli=argparse.ArgumentParser()
    cli.add_argument("--size",type=int,default=4)
    cli.add_argument("--limit",type=int,default=60)
    cli.add_argument("--budget",type=int,default=1500)
    cli.add_argument("--seed",type=int,default=234)
    args=cli.parse_args()
    rng=random.Random(args.seed)
    def emit(obj): print(json.dumps(obj),flush=True)
    seed=[0]
    for digit in Path("q9_reordered_segments_20261120/reference191.words").read_text().split()[0]:
        seed.append(seed[-1]^(1<<int(digit)))
    assert len(seed)==192 and valid(seed)
    st,w=solve(seed,tuple(range(args.size)),args.budget)
    emit(dict(control=True,status=st,verified_edges=len(w)-1 if w else None))
    bank=[list(map(int,line.split())) for line in Path("q9_onechord_expanded_800.txt").read_text().splitlines()]
    for row in rng.sample(range(len(bank)),min(args.limit,len(bank))):
        p=bank[row]
        assert len(p)==len(set(p))==193 and all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
        chord,=[(i,j) for i,v in enumerate(p) for j in range(i+2,len(p)) if (v^p[j]).bit_count()==1]
        axes=tuple(sorted(rng.sample(range(9),args.size)))
        st,w=solve(p,axes,args.budget)
        emit(dict(row=row,chord=chord,axes=axes,status=st,witness=w))
        if w: break
if __name__=="__main__":main()
