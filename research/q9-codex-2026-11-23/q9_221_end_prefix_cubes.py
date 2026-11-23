"""Cover each endpoint distance by jointly normalizing two steps at each end."""

import argparse
import json
from itertools import permutations
from pathlib import Path

from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_221_compact_selector import build_compact
from q9_endpoint_distance_bound import read_path
from q9_lazy_colour_cycles import cycle_components
from q9_tight_interface_search import certify


def normalize_moves(moves,distance):
    mapped = {}
    next_axis = [0,distance]
    for axis in moves:
        if axis not in mapped:
            group = int(axis>=distance)
            mapped[axis] = next_axis[group]
            next_axis[group]+=1
    return tuple(mapped[axis] for axis in moves),mapped


def prefixes(moves,endpoint):
    a,b,c,d = (1<<axis for axis in moves)
    return (0,a,a^b),(endpoint,endpoint^c,endpoint^c^d)


def normalize_pair(moves,distance):
    return min(normalize_moves(moves,distance)[0],
               normalize_moves(moves[2:]+moves[:2],distance)[0])


def representatives(distance):
    end = (1<<distance)-1
    pairs = list(permutations(range(9),2))
    result = set()
    for a in pairs:
        for b in pairs:
            first,last = prefixes(a+b,end)
            if all((u^v).bit_count()>=2 for u in first for v in last):
                result.add(normalize_pair(a+b,distance))
    return sorted(result)


def add_prefix_cover(formula,distance):
    pool = IDPool(start_from=formula.nv+1)
    end = (1<<distance)-1
    cases = {}
    for row in representatives(distance):
        first,last = prefixes(row,end)
        chosen = set(first+last)
        forbidden = set()
        for a,b,c in (first,last):
            forbidden.update((a^(1<<i) for i in range(9) if a^(1<<i)!=b))
            forbidden.update((b^(1<<i) for i in range(9) if b^(1<<i) not in (a,c)))
        assert not chosen&forbidden
        selector = pool.id()
        formula.extend([[-selector,u+1] for u in sorted(chosen)])
        formula.extend([[-selector,-u-1] for u in sorted(forbidden)])
        cases[row]=selector
    formula.append(list(cases.values()))
    return cases


def add_d5_terminal_face_cover(formula, signatures):
    from hashlib import sha256

    from q9_overlapping_cross18 import value_literals
    from q9_square_census import add_popcount

    raw = signatures.read_bytes()
    rows = set()
    for line in raw.splitlines():
        n, e, first, last, count = map(int, line.split())
        assert 2 <= n <= 16 and 0 <= e <= 12 and count > 0
        assert 1 <= first and 1 <= last and first + last <= n
        rows.add((n, e, first > 1, last > 1))
    assert {row[0] for row in rows} == set(range(2, 17))
    pool = IDPool(start_from=formula.nv + 1)
    population = add_popcount(formula, pool, [list(range(1, 33))])
    edges = []
    for u in range(32):
        for axis in range(5):
            v = u ^ (1 << axis)
            if v > u:
                edge = pool.id()
                edges.append(edge)
                formula.extend([[-edge, u+1], [-edge, v+1], [edge, -u-1, -v-1]])
    internal_edges = add_popcount(formula, pool, [edges])
    internal_terminal = []
    for u in (0,31):
        indicator = pool.id()
        neighbors = [(u ^ (1 << axis)) + 1 for axis in range(5)]
        formula.append([-indicator, *neighbors])
        formula.extend([[indicator, -v] for v in neighbors])
        internal_terminal.append(indicator)
    selectors = {n: pool.id() for n in range(2,17)}
    for n, selector in selectors.items():
        formula.extend([[-selector, bit] for bit in value_literals(population, n)])
    choices = []
    for n, e, first, last in sorted(rows):
        choice = pool.id()
        choices.append(choice)
        formula.append([-choice, selectors[n]])
        formula.extend([[-choice, bit] for bit in value_literals(internal_edges, e)])
        formula.extend([[-choice, bit if active else -bit]
                        for bit, active in zip(internal_terminal, (first, last))])
    formula.append(choices)
    return selectors, dict(signature_rows=len(rows), signatures_sha256=sha256(raw).hexdigest())


def run(d,budget,checker,stem,ledger,long_q5_cycles=False,terminal_face_signatures=None):
    face_partition = terminal_face_signatures is not None
    formula,end = build_compact(221,d,json.loads(ledger.read_text()),ordered=face_partition,
                                long_q5_cycles=long_q5_cycles)
    if face_partition:
        assert d == 5
        cases, metadata = add_d5_terminal_face_cover(formula, terminal_face_signatures)
        cover_name, case_label = "D5_TERMINAL_FACE_COVER", "population"
    else:
        cases, metadata = add_prefix_cover(formula,d), {}
        cover_name, case_label = "END_PREFIX_COVER", "moves"
    print(json.dumps(dict(status=cover_name+"_STARTED",distance=d,
                          cases=list(cases),clauses=len(formula.clauses),
                          budget_per_case=budget,long_q5_cycles=long_q5_cycles,**metadata)),flush=True)
    verified = []
    cycles = set()
    with Cadical195(bootstrap_with=formula) as solver:
        for index,(case,selector) in enumerate(cases.items()):
            label = {case_label: case}
            before = solver.accum_stats()["conflicts"]
            status = "UNKNOWN"
            name = stem.with_name(f"{stem.name}_case{index:02d}")
            print(json.dumps(dict(status="CASE_STARTED",index=index,**label)),flush=True)
            while (remaining:=budget-(solver.accum_stats()["conflicts"]-before))>0:
                solver.conf_budget(remaining)
                answer = solver.solve_limited(assumptions=[selector])
                if answer is None:
                    break
                if answer is False:
                    status = certify(formula,[selector],name,checker)
                    if status=="UNSAT_DRAT_VERIFIED":
                        verified.append(index)
                    break
                model = solver.get_model()
                points = {x-1 for x in model if 1<=x<=512}
                detached = cycle_components(points,9,(0,end))
                if not detached:
                    path = read_path(model,9,221,end)
                    if face_partition:
                        assert sum(v < 32 for v in path) == case
                    else:
                        first,last = prefixes(case,end)
                        assert tuple(path[:3])==first and tuple(path[-1:-4:-1])==last
                    name.with_suffix(".path").write_text(" ".join(map(str,path))+"\n")
                    status = "SAT_PATH_VERIFIED"
                    break
                for loop in detached:
                    key = tuple(loop)
                    assert key not in cycles
                    cycles.add(key)
                    clause = [-u-1 for u in loop]
                    formula.append(clause)
                    solver.add_clause(clause)
            print(json.dumps(dict(status=status,index=index,**label,cycle_cuts=len(cycles),
                                  conflicts=solver.accum_stats()["conflicts"]-before)),flush=True)
            if status=="SAT_PATH_VERIFIED":
                break
    if cycles:
        stem.with_suffix(".cycles.json").write_text(json.dumps(sorted(cycles))+"\n")
    missing = sorted(set(range(len(cases)))-set(verified))
    print(json.dumps(dict(status=cover_name+("_INCOMPLETE" if missing else "_CLOSED"),
                          distance=d,verified=verified,remaining=missing)),flush=True)


def build_ranked(length,d,moves,ledger=()):
    from q9_221_use_verified_profiles import add_triple_floors, exclude_profiles
    from q9_direction_frequency import add_frequencies
    from q9_modular_orientation import modular
    from q9_q4_forest_diagram import add_tiled_forests, DEFAULT_TILINGS

    first,last = prefixes(moves,(1<<d)-1)
    anchors = [(first[1],1),(first[2],2),(last[1],length-1),(last[2],length-2)]
    f,end = modular(9,length,d,max(1,length.bit_length()-1),
                    anchors=anchors,anchor_distances=True)
    pool = IDPool(start_from=f.nv+1)
    counts,bonds = add_frequencies(f,pool,9,length,d,ordered=False)
    if ledger:
        assert length==221
        exclude_profiles(f,counts,d,ledger,ordered=False)
        add_triple_floors(f,counts,d,ledger,ordered=False)
    pool = IDPool(start_from=f.nv+1)
    add_tiled_forests(f,pool,bonds,DEFAULT_TILINGS[:1])
    return f,end


def run_ranked(d,budget,checker,stem,ledger):
    verified = []
    rows = representatives(d)
    known = json.loads(ledger.read_text())
    print(json.dumps(dict(status="RANKED_TWO_END_COVER_STARTED",distance=d,cases=rows)),flush=True)
    for index,moves in enumerate(rows):
        formula,end = build_ranked(221,d,moves,known)
        print(json.dumps(dict(status="CASE_STARTED",index=index,moves=moves,clauses=len(formula.clauses))),flush=True)
        status = "UNKNOWN"
        target = stem.with_name(f"{stem.name}_case{index:02d}")
        with Cadical195(bootstrap_with=formula) as solver:
            solver.conf_budget(budget)
            answer = solver.solve_limited()
            if answer is False:
                status = certify(formula,[end+1],target,checker)
                if status=="UNSAT_DRAT_VERIFIED":
                    verified.append(index)
            elif answer:
                path = read_path(solver.get_model(),9,221,end)
                first,last = prefixes(moves,end)
                assert tuple(path[:3])==first and tuple(path[-1:-4:-1])==last
                target.with_suffix(".path").write_text(" ".join(map(str,path))+"\n")
                status = "SAT_PATH_VERIFIED"
            print(json.dumps(dict(status=status,index=index,moves=moves,
                                  conflicts=solver.accum_stats()["conflicts"])),flush=True)
            if answer:
                break
    missing = sorted(set(range(len(rows)))-set(verified))
    print(json.dumps(dict(status="RANKED_TWO_END_INCOMPLETE" if missing else "RANKED_TWO_END_CLOSED",
                          distance=d,verified=verified,remaining=missing)),flush=True)

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("distance",type=int,choices=(3,5,7,9))
    p.add_argument("budget",type=int)
    p.add_argument("checker")
    p.add_argument("stem",type=Path)
    p.add_argument("ledger",type=Path)
    p.add_argument("--ranked",action="store_true")
    p.add_argument("--long-q5-cycles",action="store_true")
    p.add_argument("--d5-terminal-face-signatures",type=Path)
    a=p.parse_args()
    if a.d5_terminal_face_signatures and (a.distance != 5 or a.ranked):
        p.error("Terminal-face signatures require the compact distance-five encoder")
    if a.ranked:
        if a.long_q5_cycles:
            p.error("--long-q5-cycles uses the compact encoder")
        run_ranked(a.distance,a.budget,a.checker,a.stem,a.ledger)
    else:
        run(a.distance,a.budget,a.checker,a.stem,a.ledger,a.long_q5_cycles,
            a.d5_terminal_face_signatures)
