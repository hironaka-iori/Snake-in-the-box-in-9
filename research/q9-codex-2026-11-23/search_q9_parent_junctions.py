"""Search for a longer induced path while relaxing the joins of two parent paths."""
from pathlib import Path
from itertools import combinations
import re
import argparse
import json
from search_q9_anchored_sets import search

def check(path, edges):
    assert len(path) >= edges + 1 and len(path) == len(set(path))
    assert all(0 <= v < 512 for v in path)
    assert all(((a ^ b).bit_count() == 1) == (j == i+1)
               for (i, a), (j, b) in combinations(enumerate(path), 2))

def sources(folder):
    trace = (folder / "ctrl3.log").read_text().splitlines()[0]
    pair, *path = map(int, (folder / "ctrl3.out").read_text().split())
    assert pair == int(trace.split()[2])
    check(path, 191)
    host = list(map(int,(folder / "middles.pts").read_text().splitlines()[2*pair].split()))
    anchors = [path.index(host[int(k)]) for interval in re.findall(r"tract (\d+) (\d+)",trace) for k in interval]
    assert len(anchors) == 6
    yield "ctrl3.out", pair, path, sorted(anchors)
    for name, bank in [('real191.pts','pairs.pts'), ('deep191.pts','middles.pts'),
                       ('triple191.pts','middles.pts')]:
        parents = (folder / bank).read_text().splitlines()
        for line in (folder / name).read_text().splitlines():
            pair, *p = map(int, line.split())
            check(p, 191)
            a, b = (set(map(int, parents[2*pair+i].split())) for i in range(2))
            exclusive = [(i, v in a) for i, v in enumerate(p) if (v in a) != (v in b)]
            joins = {(i+j)//2 for (i, x), (j, y) in zip(exclusive,exclusive[1:]) if x != y}
            if not joins:
                continue
            yield name, pair, p, sorted(joins)

def masks(p, joins, broad):
    width_list = [10,14] if broad else [2,4,6,8]
    for width in width_list:
        for parity in [None,0,1]:
            # Leave the two tips and both sides of every crossover free.
            centers = [0,*joins,len(p)-1]
            def anchored(i,v):
                gap = min(abs(i-j) for j in centers)
                return gap > width or (parity is not None and gap > width//2 and v.bit_count()%2==parity)
            fixed = {v for i,v in enumerate(p) if anchored(i,v)}
            if fixed:
                yield width, parity, fixed

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('folder',type=Path)
    parser.add_argument('--broad',action='store_true')
    parser.add_argument('--budget',type=int,default=1200)
    args = parser.parse_args()
    for name,pair,p,joins in sources(args.folder):
        seen = set()
        for width,parity,fixed in masks(p,joins,args.broad):
            if frozenset(fixed) in seen:
                continue
            seen.add(frozenset(fixed))
            for target in ([191,192] if parity is None and width==(10 if args.broad else 2) else [192]):
                status,witness = search(fixed,set(p),target,args.budget,at_least=True)
                if witness is not None:
                    check(witness,target)
                    assert fixed <= set(witness)
                print(json.dumps(dict(source=name,pair=pair,joins=joins,width=width,
                                      parity=parity,fixed=len(fixed),target=target,
                                      status=status,witness=witness)), flush=True)
                if witness and len(witness)>=193:
                    return
if __name__ == '__main__':
    main()
