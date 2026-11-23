"""Exact Q4 forest constraints using a reduced decision diagram."""

from functools import lru_cache


@lru_cache(maxsize=1)
def forest_masks():
    adjacency = [sum(1<<(v^(1<<axis)) for axis in range(4)) for v in range(16)]
    valid = []
    for selected in range(1<<16):
        if selected.bit_count()>8:
            continue
        points = [v for v in range(16) if selected>>v&1]
        degree = {v:(adjacency[v]&selected).bit_count() for v in points}
        if any(d>2 for d in degree.values()):
            continue
        queue = [v for v in points if degree[v]<2]
        visited = set(queue)
        for v in queue:
            for u in points:
                if u not in visited and (v^u).bit_count()==1:
                    visited.add(u)
                    queue.append(u)
        if len(visited)==len(points):
            valid.append(selected)
    return frozenset(valid)


def diagram(order, valid):
    leaves = [int(sum((1<<v) for i,v in enumerate(order) if mask>>i&1) in valid)
              for mask in range(1<<16)]
    nodes = []
    cache = {}
    for v in order:
        parent = []
        for low,high in zip(leaves[::2],leaves[1::2]):
            if low==high:
                parent.append(low)
                continue
            key = (v,low,high)
            if key not in cache:
                cache[key] = len(nodes)+2
                nodes.append(key)
            parent.append(cache[key])
        leaves = parent
    assert len(leaves)==1
    return leaves[0],nodes


@lru_cache(maxsize=1)
def forest_diagram():
    sequences = (
        tuple(range(16)),
        tuple(i^(i>>1) for i in range(16)),
        tuple(sorted(range(16),key=lambda v:(v.bit_count()%2,v))),
        tuple(sorted(range(16),key=lambda v:(v.bit_count(),v))),
    )
    return min((diagram(order,forest_masks()) for order in sequences),
               key=lambda candidate:len(candidate[1]))


def encode_forest(formula,pool,vertices,compact=False):
    root,nodes = forest_diagram()
    truth = pool.id()
    formula.append([truth])
    ids = [-truth,truth]
    for coord,lo,hi in nodes:
        sel,low,high = vertices[coord],ids[lo],ids[hi]
        active = pool.id()
        formula.extend([[-active,sel,low],[-active,-sel,high]])
        if not compact:
            formula.extend([[active,sel,-low],[active,-sel,-high]])
        ids.append(active)
    formula.append([ids[root]])


DEFAULT_TILINGS = ((0,1,2,3),(0,1,4,5),(2,3,6,7),(0,4,6,8),(1,3,5,8))


def add_tiled_forests(formula,pool,bonds=None,tilings=DEFAULT_TILINGS):
    for axes in tilings:
        offsets = [sum(1<<axis for i,axis in enumerate(axes) if label>>i&1)
                   for label in range(16)]
        mask = offsets[-1]
        for origin in range(512):
            if not (origin&mask):
                encode_forest(formula,pool,[origin+v+1 for v in offsets],compact=bonds is not None)
        if bonds is not None:
            from q9_q4_tiling_connectivity import add_tiling_connectivity
            add_tiling_connectivity(formula,pool,bonds,axes)
    return len(tilings)*32
