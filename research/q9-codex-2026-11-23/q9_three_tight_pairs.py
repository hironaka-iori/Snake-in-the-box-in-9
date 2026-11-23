"""Enumerate Q6 count profiles when three directions each occur nine times."""
import argparse
import json
from collections import defaultdict
from itertools import combinations, permutations, product

from q9_cross18_interface_profiles import SIDES, patterns
from q9_projection_interfaces import profiles as pair_profiles
from q9_three_axis_profiles import edge6

AXES = range(3)
PAIRS = tuple(combinations(AXES,2))
BONDS = tuple((u,u^(1<<a)) for a in AXES for u in range(8) if not u>>a&1)


def other(a,b):
    return 3-a-b


def low_vertices(a,b):
    return 0,1<<a,1<<b,(1<<a)|(1<<b)


def matrices(total_by_first,total_by_second):
    r,s = total_by_first
    p,q = total_by_second
    assert r+s == p+q
    for x in range(max(0,p-s),min(r,p)+1):
        yield x,p-x,r-x,s-p+x


def projection_banks(counts):
    if counts == (9,9,9):
        small = [(e,c,t) for e,c,t in patterns(True) if t[0]+t[3]==9]
        return (small,)*3
    cases = list(pair_profiles(max(counts[a]+counts[b] for a,b in PAIRS)))
    banks = []
    for a,b in PAIRS:
        pair_total = counts[a]+counts[b]
        end = counts[a]%2 + 2*(counts[b]%2)
        rows = []
        for k,target,cross,e,v in cases:
            if (k,target)==(pair_total,end) and cross[0]+cross[1]==counts[a]:
                rows.append((e,tuple(p-q for p,q in zip(v,e)),
                             tuple(cross[i] for i in (0,2,3,1))))
        banks.append(tuple(rows))
    return banks


def join_edge_counts(choices, interfaces, cross, components):
    """Split the smallest merged bank, then look up the other two margins."""
    if not all(choices):
        return
    pivot = min(range(3), key=lambda i: len(choices[i]))
    base = interfaces[pivot]
    caps = [min(edge6(c), 32-c) for c in components]
    stage = {v: i for i, bond in enumerate(base) for v in bond}
    margin_checks = [[] for _ in base]
    contact_checks = [[] for _ in base]
    for i, marginal in enumerate(interfaces):
        if i == pivot:
            continue
        previous = ()
        for depth in range(len(base)):
            known = tuple(j for j, (u, v) in enumerate(marginal)
                          if max(stage[u], stage[v]) <= depth)
            if known != previous:
                available = {tuple(row[j] for j in known) for row in choices[i]}
                margin_checks[depth].append((tuple(marginal[j] for j in known), available))
                previous = known
    for (u, v), contact in cross.items():
        if contact:
            contact_checks[max(stage[u], stage[v])].append((u, v, contact))

    edges = [0] * 8

    def extend(windows, sums, depth=0):
        if depth == len(base):
            yield tuple(edges)
            return
        u, v = base[depth]
        for left in windows[depth]:
            edges[u], edges[v] = left, sums[depth] - left
            if any(tuple(edges[a] + edges[b] + cross[a, b] for a, b in bonds)
                   not in allowed for bonds, allowed in margin_checks[depth]):
                continue
            if any(not compatible(edges[a], components[a], edges[b], components[b], r)
                   for a, b, r in contact_checks[depth]):
                continue
            yield from extend(windows, sums, depth + 1)

    for merged in choices[pivot]:
        sums = [n - cross[bond] for n, bond in zip(merged, base)]
        windows = [range(max(0, n - caps[v]), min(caps[u], n) + 1)
                   for (u, v), n in zip(base, sums)]
        yield from extend(windows, sums)


def projections(counts=(9,9,9)):
    endpoint = sum((n%2)<<i for i,n in enumerate(counts))
    banks = []
    for source in projection_banks(counts):
        grouped = defaultdict(lambda:defaultdict(set))
        for edges,components,crossings in source:
            grouped[crossings][components].add(edges)
        banks.append(grouped)
    cube_interfaces = [
        tuple((u,u|(1<<other(a,b))) for u in low_vertices(a,b)) for a,b in PAIRS
    ]
    for proposal in product(*(tuple(bank) for bank in banks)):
        by_pair = dict(zip(PAIRS,proposal))
        options = []
        for a in AXES:
            ports = []
            for b in AXES:
                if a==b:
                    continue
                t = by_pair[tuple(sorted((a,b)))]
                ports.append((t[0],t[3]) if a<b else (t[1],t[2]))
            options.append(tuple(matrices(*ports)))
        for groups in product(*options):
            links = sum(groups,())
            z = dict(zip(BONDS,links))
            incidence = [int(u==0)+int(u==endpoint)+sum(r for bond,r in z.items() if u in bond)
                         for u in range(8)]
            if any(i%2 for i in incidence):
                continue
            comps = tuple(i//2 for i in incidence)
            occupied = {u for u,c in enumerate(comps) if c}
            seen = {0}
            for _ in range(7):
                seen |= {v for (u,v),r in z.items() if r and u in seen}
                seen |= {u for (u,v),r in z.items() if r and v in seen}
            if seen != occupied:
                continue
            # The crossing layout already fixes component numbers in all
            # twelve merged layers. Join edge tuples only after this filter.
            choices = []
            for bank,crossings,interfaces in zip(banks,proposal,cube_interfaces):
                merged = tuple(comps[u]+comps[v]-z[u,v] for u,v in interfaces)
                choices.append(bank[crossings].get(merged,()))
            for e in join_edge_counts(choices,cube_interfaces,z,comps):
                yield e,comps,links


def compatible(a,ca,b,cb,r):
    if b>a:
        return compatible(b,cb,a,ca,r)
    if a == 26:
        return b <= (23 if r==1 else 22 if r==2 else 21)
    if a == b == 25:
        if r >= 3 or min(ca,cb) < 2:
            return False
        return max(ca,cb)>=3 if r==1 else min(ca,cb)>=3
    return not (a==25 and ((r>=3 and b>=24) or (r>=4 and b>=23)))


def canonical(row,counts=(9,9,9)):
    e,c,x = row
    bonds = dict(zip(BONDS,x))
    variants = []
    endpoint = sum((n%2)<<i for i,n in enumerate(counts))
    for order in permutations(AXES):
        if tuple(counts[i] for i in order)!=counts:
            continue
        for flip in (0,endpoint):
            vertices = [sum((u>>a&1)<<b for b,a in enumerate(order))^flip
                        for u in range(8)]
            variants.append((tuple(e[u] for u in vertices),tuple(c[u] for u in vertices),
                             tuple(bonds[tuple(sorted((vertices[u],vertices[v])))]
                                   for u,v in BONDS)))
    return min(variants)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('counts',type=int,nargs='*')
    args = parser.parse_args()
    counts = tuple(args.counts) or (9,9,9)
    assert len(counts)==3 and min(counts)>=3
    options = set(projections(counts))
    unique = sorted({canonical(row,counts) for row in options})
    print(json.dumps(dict(labelled=len(options),orbits=len(unique),
                          representatives=unique)))

