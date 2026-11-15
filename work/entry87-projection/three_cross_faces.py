"""Keep either pair of face paths from a three-crossing snake and rebuild the opposite face."""
import argparse
import json
from collections import Counter
from itertools import combinations
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

from solve import BANK, BANK_HASH, defects, save, sha256
from punctured_lift import project
from bank_pivots import canonical_word


def normalize(a, b):
    order = []
    for run in (a, b):
        for x, y in zip(run, run[1:]):
            bit = (x ^ y).bit_length() - 1
            if bit not in order:
                order.append(bit)
    offset = a[0] ^ b[0]
    order += sorted(set(range(8)) - set(order), key=lambda j: (offset >> j) & 1)
    def transform(x):
        return sum((((x ^ a[0]) >> j) & 1) << k for k, j in enumerate(order))
    return tuple(map(transform, a)), tuple(map(transform, b))


def catalogue():
    raw = BANK.read_bytes()
    assert sha256(raw).hexdigest() == BANK_HASH
    cases = {}
    for entry, row in enumerate(json.loads(raw)):
        source = row["vertex_sequence"]
        moves = Counter((x ^ y).bit_length()-1 for x, y in zip(source, source[1:]))
        for axis, count in moves.items():
            if count != 3:
                continue
            path, (i, j, k) = project(source, axis)
            parts = [path[:i+1], path[i:j+1], path[j:k+1], path[k:]]
            for side in (0, 1):
                a, b = parts[side::2]
                assert min(len(a), len(b)) >= 2
                assert not defects(a) and not defects(b)
                assert all((x ^ y).bit_count() >= 2 for x in a for y in b)
                key = min(normalize(x, y) for first, second in ((a,b),(b,a))
                          for x in (first,first[::-1]) for y in (second,second[::-1]))
                cases.setdefault(key, []).append(dict(entry=entry, axis=axis, side=side,
                                                       runs=list(map(len,parts)), least=min(moves.values())))
    return [dict(forest=key, occurrences=occ) for key, occ in cases.items()]


def decide(row, index, target, budget, checker=None, new=False, endpoint=None):
    a,b = row["forest"]
    fixed = set(a) | set(b)
    tips = {a[0],a[-1],b[0],b[-1]}
    allowed = set(range(256)) - (fixed - tips)
    pool = IDPool()
    use = {v: pool.id(("use",v)) for v in sorted(allowed)}
    end = {v: pool.id(("end",v)) for v in sorted(allowed)}
    clauses = []
    def exact(lits, k, guards=()):
        for c in CardEnc.equals(lits, bound=k, vpool=pool, encoding=EncType.totalizer).clauses:
            clauses.append([*guards,*c])
    exact(list(use.values()),target-len(fixed))
    exact([use[v] for v in sorted(tips)],3)
    exact(list(end.values()),1)
    if endpoint is not None:
        tip=sorted(tips)[endpoint]
        clauses.append([-use[tip]])
        for w in end:
            if (tip.bit_count()+w.bit_count())%2 != target%2:
                clauses.append([-end[w]])
    fixed_odd = sum(v.bit_count()%2 for v in fixed)
    evens = [use[v] for v in use if v.bit_count()%2 == 0]
    if target%2:
        for parity in sorted({v.bit_count()%2 for v in tips}):
            # The unique fixed endpoint selects the full path's majority colour.
            guards = [-use[v] for v in sorted(tips) if v.bit_count()%2 != parity]
            exact(evens,target//2+parity-fixed_odd,guards)
    else:
        exact(evens,target//2-fixed_odd)
    for v in use:
        neighbours = [use[w] for j in range(8) if (w:=v^(1<<j)) in use]
        degree = neighbours + [end[v]]
        needed = 1 if v in tips else 2
        clauses.append([-end[v],use[v]])
        for group in combinations(degree,needed+1):
            clauses.append([-use[v],*[-x for x in group]])
        for group in combinations(degree,len(degree)-needed+1):
            clauses.append([-use[v],*group])
    name = f"three-cross-face-{index}-{target}-{budget}" + ("-new" if new else "")
    if endpoint is not None:
        name+=f"-tip{endpoint}"
    known = {canonical_word(r["vertex_sequence"]):i for i,r in enumerate(json.loads(BANK.read_bytes()))} if new else {}
    blocked_known = []
    status = "OPEN"
    witness = None
    removed = []
    with Solver(name="cadical195",bootstrap_with=clauses,with_proof=bool(checker)) as sat:
        while (remaining:=budget-sat.accum_stats()["conflicts"]) > 0:
            sat.conf_budget(remaining)
            answer = sat.solve_limited()
            if answer is not True:
                status = "UNSAT" if answer is False else "OPEN"
                break
            model = set(sat.get_model())
            full = fixed | {v|256 for v in use if use[v] in model}
            graph = {v:{v^(1<<j) for j in range(9)} & full for v in full}
            endpoints = [v for v in full if len(graph[v])==1]
            assert len(full)==target and len(endpoints)==2 and all(1<=len(ns)<=2 for ns in graph.values())
            path = [endpoints[0]]
            visited = set(path)
            while (tail:=graph[path[-1]] - visited):
                assert len(tail)==1
                path.append(tail.pop());visited.add(path[-1])
            if len(path)==target:
                assert not defects(path)
                key=canonical_word(path)
                if key in known:
                    selected=sorted(v for v in use if use[v] in model)
                    cut=[-use[v] for v in selected]
                    sat.add_clause(cut);clauses.append(cut)
                    blocked_known.append(dict(entry=known[key],outside=selected))
                    continue
                status="FOUND";witness=path
                break
            rest=full-visited
            while rest:
                first=rest.pop();todo=[first];cycle={first}
                while todo:
                    fresh=graph[todo.pop()] & rest
                    todo.extend(fresh);rest-=fresh;cycle|=fresh
                assert all(len(graph[v]&cycle)==2 for v in cycle)
                outer=sorted(v^256 for v in cycle if v>=256)
                assert outer
                cut=[-use[v] for v in outer]
                sat.add_clause(cut);clauses.append(cut);removed.append(outer)
        report=dict(index=index,target=target,status=status,forest=row["forest"],
                    stats=sat.accum_stats(),cycles=removed,witness=witness,blocked_known=blocked_known)
        if endpoint is not None:
            report["fixed_endpoint"]=sorted(tips)[endpoint]
        if checker and status=="UNSAT":
            from export_drat import checked_export
            report.update(checked_export(sat,clauses,Path(name+"-proof"),checker))
    save(Path(name+("-checked" if checker else "")+".json"),report)
    print(index,target,status,report["stats"]["conflicts"],flush=True)


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--start",type=int,default=0)
    parser.add_argument("--stop",type=int,default=0)
    parser.add_argument("--target",type=int,choices=(192,193),default=193)
    parser.add_argument("--budget",type=int,default=400000)
    parser.add_argument("--checker",type=Path)
    parser.add_argument("--new",action="store_true")
    parser.add_argument("--endpoint",type=int,choices=range(4))
    args=parser.parse_args()
    rows=catalogue()
    if not args.stop:
        save(Path("three-cross-faces-menu.json"),rows)
        print(len(rows),sum(len(row["occurrences"]) for row in rows))
    for i in range(args.start,min(args.stop,len(rows))):
        decide(rows[i], i, args.target, args.budget, args.checker.resolve() if args.checker else None,args.new,args.endpoint)
