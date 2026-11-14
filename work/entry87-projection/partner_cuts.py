"""Generate all induced-cycle clauses inside each four-dimensional face."""
from itertools import combinations


def abstract_cycles(dim=4):
    n=1<<dim
    graph=[[v^(1<<i) for i in range(dim)] for v in range(n)]
    neighbours=[set(row) for row in graph]
    cycles=set()
    # The smallest vertex fixes the start. Each orientation leads to the same
    # vertex-set clause. An extension touching the start already closes a cycle.
    for root in range(n):
        def visit(path,used):
            for nxt in graph[path[-1]]:
                if nxt<=root or nxt in used:continue
                touched=neighbours[nxt]&used
                if touched=={path[-1]}:
                    visit(path+[nxt],used|{nxt})
                elif len(path)>=3 and touched=={root,path[-1]}:
                    cycles.add(tuple(sorted(used|{nxt})))
        visit([root],{root})
    return sorted(cycles)


def add_subcube_cuts(root,allowed,graph,var,sat):
    universe=set(allowed)
    # Square and six-cycle clauses already appear in the pinned graph report
    # when supported on <=3 directions. These longer clauses use new information.
    patterns=[c for c in abstract_cycles() if len(c)>=8]
    seen=set()
    for directions in combinations(range(8),4):
        mask=sum(1<<i for i in directions)
        translated=[sum(((x>>i)&1)<<v for i,v in enumerate(directions)) for x in range(16)]
        for base in range(256):
            if base&mask:continue
            for cycle in patterns:
                if any((base|translated[x]) not in universe for x in cycle):continue
                concrete=tuple(sorted(base|translated[x] for x in cycle))
                if concrete in seen:continue
                vertices=set(concrete)
                assert all(len(vertices.intersection(graph[v]))==2 for v in concrete)
                sat.add_clause([-var[v] for v in concrete]);seen.add(concrete)
    return len(seen)
