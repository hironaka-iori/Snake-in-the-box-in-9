"""Classify all maximal families of mutually touching nonempty subsets of Q3."""
from collections import Counter
from itertools import combinations,permutations
from pathlib import Path
import argparse
import json
from solve import save


def neighbourhood(s):
    return sum(1<<y for y in range(8) if any(s>>x&1 and (x^y).bit_count()<=1 for x in range(8)))


def data():
    nbr=[neighbourhood(s) for s in range(256)]
    pairs=[s for s in range(1,256) if s.bit_count()==2]
    opposite=lambda s:255^nbr[s]
    # Each two-point shape with a nonempty far set has one unique far two-point shape.
    choices=[(s,opposite(s)) for s in pairs if opposite(s) and s<opposite(s)]
    assert len(choices)==12 and all(opposite(t)==s for s,t in choices)
    universal=[s for s in pairs if not opposite(s)]
    assert len(universal)==4
    sgl=[1<<x for x in range(8)]
    # Each singleton has just one largest far set, of size four. Any of its
    # nonempty subsets can conflict with the singleton.
    return nbr,choices,universal,sgl


def complete_pair_patterns():
    nbr,choices,universal,sgl=data()
    patterns=[]
    for code in range(4096):
        raw=universal+[pair[(code>>i)&1] for i,pair in enumerate(choices)]
        singles=[s for s in sgl if all(nbr[s]&t for t in raw)]
        assert all(nbr[s]&t for s,t in combinations(singles,2))
        minimal=tuple(sorted(singles+[t for t in raw if not any(t&s for s in singles)]))
        patterns.append(minimal)
    assert len(set(patterns))==4096
    return patterns


def maximal_full(pattern,selected=None):
    # Upward closure from size <=2 can now add large sets. Two three-or-more
    # point shapes always touch. A large shape is compatible with every
    # two-point shape, and can be forbidden only by a singleton.
    singles=[s for s in pattern if s.bit_count()==1]
    if selected is None:
        selected=singles
    # The oriented pairs are reconstructed by upward closure in the small
    # family before optionally omitting its compatible singletons.
    return tuple(s for s in range(1,256) if (s in selected)
                 or (s.bit_count()==2 and any(t&s==t for t in pattern))
                 or (s.bit_count()>=3 and all(neighbourhood(v)&s for v in selected)))


def compressed_full_masks():
    patterns=complete_pair_patterns()
    covered={v:0 for v in range(1,256)}
    family_count=0
    for p in patterns:
        singles=[s for s in p if s.bit_count()==1]
        for size in range(len(singles)+1):
            for chosen in combinations(singles,size):
                for s in maximal_full(p,chosen):
                    covered[s]|=1<<family_count
                family_count+=1
    return family_count,covered


def maximum_score(traces):
    """Exact clique number, including all multiplicities, in 21 simple cases."""
    weights=Counter(traces)
    nbr,pairs,universals,singles=data()
    choices=[()]+[(s,) for s in singles]+[(a,b) for a,b in combinations(singles,2) if nbr[a]&b]
    best=-1
    witness=None
    for selected in choices:
        def ok(t):
            return all(nbr[s]&t for s in selected)
        shapes=list(selected)
        shapes.extend(s for s in weights if s.bit_count()>=3 and ok(s))
        shapes.extend(s for s in universals if ok(s))
        for a,b in pairs:
            eligible=[v for v in (a,b) if ok(v)]
            if eligible:
                shapes.append(max(eligible,key=lambda v:weights[v]))
        score=sum(weights[s] for s in shapes)
        if score>best:
            best=score;witness=shapes
    return best,witness


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--out",type=Path)
    args=parser.parse_args()
    pats=complete_pair_patterns()
    stats=Counter((sum(s.bit_count()==1 for s in p),len(p)) for p in pats)
    print(stats)
    if args.out:
        save(args.out,dict(patterns=len(pats),type_counts=[dict(singletons=k[0],minimal_small_shapes=k[1],n=v)
                                                            for k,v in sorted(stats.items())]))
