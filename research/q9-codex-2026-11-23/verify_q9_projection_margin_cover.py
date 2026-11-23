"""Independently enumerate Q3 seam multiplicities and Q6 edge allocations."""

import argparse
from collections import defaultdict
from itertools import product
import json
from pathlib import Path

from q9_projection_interfaces import profiles
from q9_three_axis_profiles import edge6
from q9_three_tight_pairs import canonical, compatible


AXIS_BONDS = tuple(
    tuple((u,u | (1 << axis)) for u in range(8) if u & (1 << axis) == 0)
    for axis in range(3)
)
PAIRS = ((0,1),(0,2),(1,2))
SEAMS = tuple(bond for bank in AXIS_BONDS for bond in bank)


def compositions(total):
    return [
        (a,b,c,total-a-b-c)
        for a in range(total+1) for b in range(total-a+1)
        for c in range(total-a-b+1)
    ]


def margin_data(counts):
    pairs = defaultdict(lambda: defaultdict(set))
    for total,end,crossings,edges,vertices in profiles(sum(sorted(counts)[-2:])):
        for a,b in PAIRS:
            if total!=counts[a]+counts[b] or end!=counts[a]%2+2*(counts[b]%2):
                continue
            if crossings[0]+crossings[1]!=counts[a]:
                continue
            comps = tuple(v-e for v,e in zip(vertices,edges))
            pairs[a,b][(crossings[0],crossings[2],comps)].add(edges)
    return pairs


def audit(counts, saved):
    banks = margin_data(counts)
    groups = [compositions(n) for n in counts]
    zero_parts = {
        (axis,other,group):sum(n for (u,_),n in zip(AXIS_BONDS[axis],group) if u & (1<<other) == 0)
        for axis in range(3) for other in range(3) if axis!=other for group in groups[axis]
    }
    possible = {pair:{key[:2] for key in bank} for pair,bank in banks.items()}
    layouts = 0
    labelled = 0
    seen = set()
    target = 221-sum(counts)
    end = sum((n%2)<<axis for axis,n in enumerate(counts))
    for x in groups[0]:
        ys = [y for y in groups[1] if (zero_parts[0,1,x],zero_parts[1,0,y]) in possible[0,1]]
        zs = [z for z in groups[2] if (zero_parts[0,2,x],zero_parts[2,0,z]) in possible[0,2]]
        for y,z in product(ys,zs):
            if (zero_parts[1,2,y],zero_parts[2,1,z]) not in possible[1,2]:
                continue
            crossing = dict(zip(SEAMS,x+y+z))
            incidence = [int(v==0)+int(v==end) for v in range(8)]
            connected = {0}
            for (u,v),n in crossing.items():
                incidence[u] += n
                incidence[v] += n
            if any(n%2 for n in incidence):
                continue
            for _ in range(7):
                for (u,v),n in crossing.items():
                    if n and (u in connected or v in connected):
                        connected.update((u,v))
            if len(connected) != sum(n>0 for n in incidence):
                continue
            components = [n//2 for n in incidence]
            allowed = []
            for a,b in PAIRS:
                other = 3-a-b
                pairs = AXIS_BONDS[other]
                merged = tuple(components[u]+components[v]-crossing[u,v] for u,v in pairs)
                crossing_a = zero_parts[a,b,(x,y,z)[a]]
                crossing_b = zero_parts[b,a,(x,y,z)[b]]
                positions = banks[a,b].get((crossing_a,crossing_b,merged))
                if not positions:
                    break
                allowed.append((pairs,positions))
            if len(allowed)!=3:
                continue
            layouts += 1
            caps = [min(edge6(c),32-c) for c in components]
            sums = {bond:{row[i]-crossing[bond] for row in records}
                    for pairs,records in allowed for i,bond in enumerate(pairs)}

            def fill(edges, remaining):
                v = len(edges)
                if v==8:
                    if all(tuple(edges[u]+edges[w]+crossing[u,w] for u,w in pairs) in records
                           for pairs,records in allowed):
                        yield tuple(edges)
                    return
                values = set(range(max(0,remaining-sum(caps[v+1:])),min(caps[v],remaining)+1))
                for u in range(v):
                    if (u,v) not in crossing:
                        continue
                    values.intersection_update(n-edges[u] for n in sums[u,v])
                    if crossing[u,v]:
                        values = {n for n in values if compatible(edges[u],components[u],n,components[v],crossing[u,v])}
                for n in values:
                    yield from fill(edges+[n],remaining-n)

            for e in fill([],target):
                seen.add(canonical((e,tuple(components),x+y+z),counts))
                labelled += 1

    expected = {tuple(tuple(items) for items in row) for row in saved["representatives"]}
    assert labelled==saved["labelled"] and seen==expected, (labelled,len(seen),len(expected),len(seen-expected),len(expected-seen))
    return dict(status="MARGIN_COVER_VERIFIED",counts=counts,layouts=layouts,labelled=labelled,orbits=len(seen))


def audit_screen(counts, saved, screen):
    """Check every omitted orbit against the closed local-obstruction ledger."""
    from q9_221_global_interface_cuts import load_cuts
    from q9_three_tight_star_refine import excludes

    rows = saved["representatives"]
    assert tuple(screen["counts"]) == counts and screen["source_orbits"] == len(rows)
    keep = set(screen["colour_survivors"])
    assert len(keep) == len(screen["colour_survivors"]) and keep <= set(range(len(rows)))
    exact, stars = load_cuts()
    forbidden = {(tuple(a),tuple(b),k) for x,y,k in exact for a,b in ((x,y),(y,x))}
    witnesses = {}
    for i,row in enumerate(rows):
        if i in keep:
            continue
        e,c,cross = row
        for (u,v),n in zip(SEAMS,cross):
            key = ((e[u],c[u]),(e[v],c[v]),n)
            if key in forbidden:
                witnesses[i] = dict(kind="pair", layers=(u,v), key=key)
                break
        if i not in witnesses:
            key = next((star for star in stars if excludes(row,star)),None)
            if key is not None:
                witnesses[i] = dict(kind="star", key=key)
    unresolved = sorted(set(range(len(rows)))-keep-witnesses.keys())
    return keep,witnesses,unresolved


def verify_colour_exceptions(counts, rows, indices, args):
    from q9_colour_screen_profiles import pinned
    from q9_colour_three_axis import capacity_table, colour_formula, interface_table
    from q9_tight_interface_search import certify

    end = sum((n%2)<<axis for axis,n in enumerate(counts))
    formula,*banks = colour_formula(counts,end,capacity_table(args.capacity),
                                    interface_table(args.interfaces))
    verified = {}
    for index in indices:
        stem = args.witnesses.with_name(args.witnesses.stem+f"_colour_{index}")
        status = certify(formula,pinned(*banks,rows[index]),stem,args.checker)
        assert status=="UNSAT_DRAT_VERIFIED", (index,status)
        verified[index] = dict(kind="colour_drat", proof=stem.with_suffix(".drat").name,
                               formula=stem.with_suffix(".cnf").name)
    return verified


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("counts",type=int,nargs=3)
    parser.add_argument("profiles",type=Path)
    parser.add_argument("--screen",type=Path)
    parser.add_argument("--witnesses",type=Path)
    parser.add_argument("--capacity",type=Path)
    parser.add_argument("--interfaces",type=Path)
    parser.add_argument("--checker")
    args = parser.parse_args()
    counts = tuple(args.counts)
    saved = json.loads(args.profiles.read_text())
    result = audit(counts,saved)
    print(json.dumps(result),flush=True)
    if args.screen:
        assert args.witnesses is not None
        keep,witnesses,unresolved = audit_screen(counts,saved,json.loads(args.screen.read_text()))
        if unresolved and args.checker:
            assert args.capacity and args.interfaces
            verified = verify_colour_exceptions(counts,saved["representatives"],unresolved,args)
            witnesses.update(verified)
            unresolved = sorted(set(unresolved)-verified.keys())
        args.witnesses.write_text(json.dumps(witnesses)+"\n")
        status = "VERIFIED" if not unresolved else "UNRESOLVED_LOCAL_SCREEN"
        print(json.dumps(dict(status=status,counts=counts,orbits=len(keep),
                              starting_orbits=result["orbits"],excluded=len(witnesses),
                              unresolved=unresolved)),flush=True)
