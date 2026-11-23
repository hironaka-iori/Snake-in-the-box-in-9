"""Verify geodesic completion of specified, ordered Q9 anchors by SAT."""
import collections
import sys
from pysat.solvers import Minicard

def complete(anchors):
    pool = collections.defaultdict(list)
    stages = []
    var = 0
    with Minicard() as solver:
        for gap, (a, b) in enumerate(zip(anchors, anchors[1:])):
            mask = a ^ b
            h = mask.bit_count()
            for depth in range(1, h):
                layer = {}
                delta = mask
                while delta:
                    x = a ^ delta
                    if delta.bit_count() == depth and x not in anchors and all((x ^ v).bit_count() != 1 for v in anchors if v != a and v != b):
                        var += 1
                        layer[x] = var
                        pool[x].append((gap, var))
                    delta = (delta - 1) & mask
                solver.add_clause(list(layer.values()))
                if layer:
                    solver.add_atmost(list(layer.values()), 1)
                if depth > 1:
                    previous = stages[-1][1]
                    for x, lit in layer.items():
                        solver.add_clause([-lit] + [previous[y] for y in (x ^ (1 << d) for d in range(9)) if y in previous])
                stages.append((gap, layer))
        for x, entries in pool.items():
            for y in [x] + [x ^ (1 << d) for d in range(9) if not x & (1 << d)]:
                for g, lit in entries:
                    for g2, other in pool.get(y, []):
                        if g != g2:
                            solver.add_clause([-lit, -other])
        if not solver.solve():
            return None
        model = set(solver.get_model() or [])
        fill = collections.defaultdict(list)
        for gap, layer in stages:
            fill[gap].append(next(x for x, lit in layer.items() if lit in model))
        path = [anchors[0]]
        for gap, b in enumerate(anchors[1:]):
            path.extend(fill[gap])
            path.append(b)
        assert len(set(path)) == len(path)
        assert all(((x ^ path[j]).bit_count() == 1) == (j == i+1) for i,x in enumerate(path) for j in range(i+1,len(path)))
        return path

if __name__ == '__main__':
    assert len(complete([0,5,7])) == 4
    tested = 0
    for line in sys.stdin:
        if not line.startswith('CAPPED '):
            continue
        anchors = list(map(int,line.split()[1:]))
        result = complete(anchors)
        tested += 1
        if result is not None:
            print('FOUND',len(result)-1,*result,flush=True)
            break
    else:
        print('DONE',tested,'UNSAT')
