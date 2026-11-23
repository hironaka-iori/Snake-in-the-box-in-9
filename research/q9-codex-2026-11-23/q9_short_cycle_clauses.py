"""Materialize every induced cycle contained in a face of at most four axes."""
from functools import lru_cache
from itertools import combinations


@lru_cache(maxsize=None)
def local_cycle_patterns(dim):
    result=[]
    vertex_count=1<<dim
    for mask in range(1<<vertex_count):
        if mask.bit_count()<4 or mask.bit_count()%2:
            continue
        selected={v for v in range(vertex_count) if mask>>v&1}
        start=min(selected)
        span=0
        for v in selected:
            span|=v^start
        if span!=vertex_count-1:
            continue
        adjacency={v:{v^(1<<axis) for axis in range(dim)}&selected for v in selected}
        if any(len(ns)!=2 for ns in adjacency.values()):
            continue
        work=[start]
        seen={start}
        for v in work:
            for w in adjacency[v]-seen:
                work.append(w)
                seen.add(w)
        if seen==selected:
            result.append(tuple(sorted(selected)))
    return tuple(result)


def add_small_cycles(f,dim,maximum_span):
    counts={}
    for span in range(2,min(dim,maximum_span)+1):
        patterns=local_cycle_patterns(span)
        counts[span]=0
        for axes in combinations(range(dim),span):
            mask=sum(1<<d for d in axes)
            mapped=[sum((1<<d) for i,d in enumerate(axes) if v>>i&1)
                    for v in range(1<<span)]
            for origin in range(1<<dim):
                if origin&mask:
                    continue
                for cycle in patterns:
                    f.append([-(origin|mapped[v])-1 for v in cycle])
                    counts[span]+=1
    return counts
