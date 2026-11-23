"""Open the 192-vertex Q9 coil by freeing an arbitrary union of parallel Q6 faces."""
import argparse
from itertools import combinations
import json
from pathlib import Path
import random
from retry_q9_six_cube_sites_cadical import search
from verify_q9_six_cube_coverage import pairwise


def cases(cycle, width):
    all_points = set(range(512))
    representatives = {}
    for axes in combinations(range(9), 3):
        cell = [sum(((x >> axis) & 1) << k for k, axis in enumerate(axes)) for x in range(512)]
        for ids in combinations(range(8), width):
            domain = frozenset(x for x in all_points if cell[x] in ids)
            representatives.setdefault(domain, (axes, ids))
    entries = list(representatives.items())
    random.Random(26549).shuffle(entries)
    for domain, (axes, ids) in entries:
        yield set(cycle) - domain, domain, axes, ids


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('width',type=int)
    parser.add_argument('target',type=int)
    parser.add_argument('conflicts',type=int)
    args=parser.parse_args()
    cycle=json.loads(Path('q9_coil_open_191_witness.json').read_text())['cycle']
    assert len(set(cycle))==len(cycle)==192
    assert all(((v^cycle[j]).bit_count()==1) == (j-i in (1,191))
               for i,v in enumerate(cycle) for j in range(i+1,len(cycle)))
    for fixed,domain,axes,ids in cases(cycle,args.width):
        status,witness=search(fixed,set(cycle),args.target,args.conflicts,allowed=fixed|domain)
        if witness:
            pairwise(witness,len(witness)-1)
            assert len(witness)>=args.target+1 and set(witness)-domain==fixed
        print(json.dumps(dict(axes=axes,cells=ids,fixed=len(fixed),target=args.target,status=status,witness=witness),separators=(',',':')),flush=True)
        if witness:break
