"""Color/partition lower bound for contracted intervals of each parity."""
from functools import lru_cache
from itertools import combinations
import argparse
import json
from pathlib import Path
from time import monotonic
from solve import paths, save


def components_partition(path,bits):
    mask=sum(1<<c for c in bits)
    z=[x&~mask for x in path]
    slices=[[z[0]]]
    for a,b in zip(z,z[1:]):
        if a==b:
            slices.append([])
        slices[-1].append(b)
    return slices


def cover_bound(slices, dimension):
    # Contracted traces with the same free word must be disjoint and have
    # no edge between any two traces in the retained cube.
    sites=sorted({z for part in slices for z in part})
    addresses={z:i for i,z in enumerate(sites)}
    types=sorted(set(tuple(sorted(part)) for part in slices))
    traces=[sum(1<<addresses[z] for z in part) for part in types]
    halo=[sum(1<<j for j,y in enumerate(sites) if any((x^y).bit_count()<=1 for x in part))
          for part in types]
    multiplicity=[sum(tuple(sorted(p))==t for p in slices) for t in types]
    assert len(sites)<=8
    # All patterns: any independent group of distinct types. A given type
    # cannot occur twice for one color because both copies occupy its sites.
    groups=[]
    def extend(start,blocked,selected):
        if selected:
            groups.append(tuple(selected))
        for j in range(start,len(types)):
            if not traces[j]&blocked:
                extend(j+1,blocked|halo[j],selected+[j])
    extend(0,0,[])
    return types,traces,multiplicity,groups


def dual_bound(slices,dimension):
    from scipy.optimize import linprog
    import numpy as np
    from fractions import Fraction
    types,traces,mult,groups=cover_bound(slices,dimension)
    matrix=np.zeros((len(groups),len(types)))
    for i,group in enumerate(groups):
        matrix[i,list(group)]=1
    result=linprog(-np.array(mult),A_ub=matrix,b_ub=np.ones(len(groups)),
                   bounds=(0,None),method="highs")
    if not result.success:
        raise RuntimeError(result.message)
    weights=[Fraction(float(w)).limit_denominator(1000) for w in result.x]
    # Normalize against the exact worst group; the resulting rational dual
    # is feasible irrespective of the floating-point solver.
    maximum=max(sum(weights[i] for i in group) for group in groups)
    weights=[w/maximum for w in weights]
    assert all(w>=0 for w in weights) and all(sum(weights[i] for i in g)<=1 for g in groups)
    score=sum(w*m for w,m in zip(weights,mult))
    return dict(value=str(score),words_available=2**(dimension-1),n_types=len(types),
                n_groups=len(groups),weights=[dict(trace=list(t),mult=m,weight=str(w))
                                              for t,m,w in zip(types,mult,weights) if w])


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--output",type=Path,required=True)
    args=ap.parse_args()
    _,target=paths()
    report=[]
    for bits in combinations(range(9),6):
        slices=components_partition(target,bits)
        assert all(len(set(s))==len(s) for s in slices)
        row=dict(bits=list(bits),parities=[dual_bound(slices[p::2],6) for p in (0,1)])
        report.append(row)
    save(args.output,report)
    from fractions import Fraction
    print(sorted(((max(Fraction(p["value"]) for p in r["parities"]),r["bits"])
                  for r in report),reverse=True)[:12])


if __name__=="__main__":
    main()
