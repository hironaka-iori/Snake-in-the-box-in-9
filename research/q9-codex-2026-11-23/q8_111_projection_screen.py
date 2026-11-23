"""Screen two-axis projections of dense Q8 forests using Q6 interface proofs."""

import argparse
from collections import Counter
from functools import lru_cache
import json
from pathlib import Path

from q9_extend_geometry_screen import canonical_patterns, compile_patterns
from q9_projection_interfaces import compatible as compatible_q7
from q9_three_axis_profiles import edge6
from q9_three_tight_pairs import BONDS, compatible
from verify_q9_free_dimension_cuts import edge7


Q2_BONDS = ((0, 1), (2, 3), (0, 2), (1, 3))
POSITIONS = dict((bond, BONDS.index(bond)) for bond in Q2_BONDS)


def compositions(total, length):
    if length == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for tail in compositions(total - first, length - 1):
                yield (first, *tail)


@lru_cache(maxsize=None)
def capacities(components):
    return tuple(min(edge6(c), 32-c) for c in components)


def cases(components):
    edges = 111-components
    for first in range(max(0, edges-104), edges//8+1):
        for second in range(first, min(edges//4-first, (edges-first)//7)+1):
            inside = edges-first-second
            for a in range(first+1):
                for c in range(second+1):
                    links = a, first-a, c, second-c
                    incident = tuple(sum(n for bond, n in zip(Q2_BONDS, links) if u in bond)
                                     for u in range(4))
                    least = tuple((n+1)//2 for n in incident)
                    slack = components+first+second-sum(least)
                    for extra in compositions(slack, 4):
                        components6 = tuple(lo+n for lo, n in zip(least, extra))
                        caps = capacities(components6)
                        if sum(caps)<inside:
                            continue
                        between = tuple(components6[u]+components6[v]-r
                                        for (u,v),r in zip(Q2_BONDS,links))
                        maxima = tuple(map(edge7,between))
                        if maxima[0]+maxima[1]<inside+first or maxima[2]+maxima[3]<inside+second:
                            continue
                        for loss in compositions(sum(caps)-inside,4):
                            e = tuple(cap-n for cap,n in zip(caps,loss))
                            if min(e)<0:
                                continue
                            merged=tuple(e[u]+e[v]+r for (u,v),r in zip(Q2_BONDS,links))
                            if any(value>upper for value,upper in zip(merged,maxima)):
                                continue
                            if not compatible_q7((*merged[:2],0,0),(*between[:2],0,0),(second,0,0,0)):
                                continue
                            if not compatible_q7((*merged[2:],0,0),(*between[2:],0,0),(first,0,0,0)):
                                continue
                            if any(r and not compatible(e[u],components6[u],e[v],components6[v],r)
                                   for (u,v),r in zip(Q2_BONDS,links)):
                                continue
                            yield (first,second),e,components6,links


def run(components, files):
    patterns=set()
    for file in files:
        patterns.update(canonical_patterns(file))
    # Each file was proved using only the displayed layers and their internal
    # interfaces. No terminal-position or whole-path conditions may be used here.
    checks={shape:rows for shape,rows in compile_patterns(patterns).items()
            if all(u<4 for u in shape[0]) and all(BONDS[b] in POSITIONS for b in shape[1])}
    before,after=Counter(),Counter()
    for profile,e,c,r in cases(components):
        before[profile]+=1
        link_values=dict(zip(POSITIONS.values(),r))
        f=tuple(zip(e,c))
        if any((tuple(f[u] for u in faces),tuple(link_values[b] for b in links)) in rows
               for (faces,links),rows in checks.items()):
            continue
        after[profile]+=1
    print(json.dumps(dict(status="PROJECTION_SCREEN",components=components,
                          tested=sum(before.values()),remaining=sum(after.values()),
                          by_frequency=[(p,n,after[p]) for p,n in sorted(before.items())])),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("components",type=int,choices=(2,3))
    parser.add_argument("patterns",type=Path,nargs="+")
    args=parser.parse_args()
    run(args.components,args.patterns)
