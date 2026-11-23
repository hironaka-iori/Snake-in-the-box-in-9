"""Enumerate necessary Q6-layer data for a two-component induced Q8 forest."""

import argparse
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path

from q9_screen_certified_interfaces import empty_interfaces
from q9_three_axis_profiles import edge6
from verify_q8_forest_bank import decode
from verify_q9_free_dimension_cuts import edge7

BONDS = ((0,1),(2,3),(0,2),(1,3))


def defects(left, layers=4):
    if layers == 1:
        yield (left,)
        return
    for value in range(left+1):
        for tail in defects(left-value,layers-1):
            yield (value,*tail)


def components_and_endpoints(incident, seam_counts):
    adj = [set() for _ in incident]
    for (a,b),n in zip(BONDS,seam_counts):
        if n:
            adj[a].add(b)
            adj[b].add(a)
    for ends in defects(4):
        if any((cross+end)%2 for cross,end in zip(incident,ends)):
            continue
        counts = tuple((cross+end)//2 for cross,end in zip(incident,ends))
        unseen = {a for a,n in enumerate(counts) if n}
        while unseen:
            root = min(unseen)
            region = {root}
            pending = [root]
            while pending:
                ahead = adj[pending.pop()]-region
                pending.extend(ahead)
                region.update(ahead)
            unseen -= region
            end_count = sum(ends[a] for a in region)
            if end_count < 2 or end_count%2:
                break
        else:
            yield counts,ends


def rows(total, blocked=()):
    for first in range(total//8+1):
        for second in range(first,(total-first)//7+1):
            internal = total-first-second
            for left in range(first+1):
                for right in range(second+1):
                    seams = (left,first-left,right,second-right)
                    incident = (seams[0]+seams[2],seams[0]+seams[3],
                                seams[1]+seams[2],seams[1]+seams[3])
                    for counts,ends in components_and_endpoints(incident,seams):
                        cap = tuple(min(edge6(c),32-c) for c in counts)
                        if sum(cap) < internal:
                            continue
                        margins = tuple(min(edge7(counts[a]+counts[b]-r),64-counts[a]-counts[b]+r)-r
                                        for (a,b),r in zip(BONDS,seams))
                        if min(margins)<0 or min(margins[0]+margins[1],margins[2]+margins[3])<internal:
                            continue
                        for v0,v1,v2 in product(*(range(max(0,internal-sum(cap)+u),u+1)
                                                   for u in cap[:3])):
                            edges = (v0,v1,v2,internal-v0-v1-v2)
                            if not 0<=edges[3]<=cap[3]:
                                continue
                            if any(edges[a]+edges[b]>m for (a,b),m in zip(BONDS,margins)):
                                continue
                            if any((edges[a],counts[a],edges[b],counts[b],n) in blocked
                                   for (a,b),n in zip(BONDS,seams)):
                                continue
                            yield first,second,edges,counts,seams,ends


def witness_projection(a,b):
    paths = (a,b)
    steps = [(u,v) for path in paths for u,v in zip(path,path[1:])]
    totals = Counter((u^v).bit_length()-1 for u,v in steps)
    x,y = sorted(range(8),key=lambda i:totals[i])[:2]
    layer = lambda u: ((u>>x)&1)+2*((u>>y)&1)
    edges = [0]*4
    seams = [0]*4
    for u,v in steps:
        first,second = layer(u),layer(v)
        if first == second:
            edges[first] += 1
        else:
            seams[BONDS.index(tuple(sorted((first,second))))] += 1
    population = Counter(map(layer,a+b))
    counts = [population[i]-e for i,e in enumerate(edges)]
    endpoints = Counter(layer(v) for p in paths for v in (p[0],p[-1]))
    return totals[x],totals[y],tuple(edges),tuple(counts),tuple(seams),tuple(endpoints[i] for i in range(4))


def run(args):
    forbidden = set().union(*(empty_interfaces(stem) for stem in args.catalogue))
    if args.control:
        with args.control.open() as source:
            checked = [witness_projection(*decode(line)) for line in source]
        by_length = {}
        for row in checked:
            total = sum(row[2])+sum(row[4])
            if total not in by_length:
                by_length[total] = set(rows(total,forbidden))
            assert row in by_length[total],row
        print(json.dumps(dict(status="CONTROL_OK",checked=len(checked))),flush=True)

    for total in args.edges:
        counted = Counter((first,second) for first,second,*_ in rows(total,forbidden))
        result = dict(status="NECESSARY_PROFILES_ENUMERATED",edges=total,total_profiles=sum(counted.values()),
                      by_minimum_directions=[[list(key),n] for key,n in sorted(counted.items())])
        print(json.dumps(result),flush=True)


if __name__=="__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("edges",type=int,nargs="+")
    parser.add_argument("--catalogue",type=Path,action="append",default=[])
    parser.add_argument("--control",type=Path)
    run(parser.parse_args())
