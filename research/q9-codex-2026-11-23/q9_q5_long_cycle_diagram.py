"""Compact forbidden-subset encoding for every 14-cycle in Q5."""

from functools import lru_cache


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length()-1
        mask -= low


@lru_cache(maxsize=1)
def long_cycles():
    adjacency = [sum(1<<(v^(1<<axis)) for axis in range(5)) for v in range(32)]
    rooted = set()

    def walk(last,chosen):
        for v in bits(adjacency[last]&~chosen):
            adjacent = adjacency[v]&chosen
            if adjacent==1<<last:
                if chosen.bit_count()<13:
                    walk(v,chosen|(1<<v))
            elif adjacent==((1<<last)|1) and chosen.bit_count()==13:
                rooted.add(chosen|(1<<v))

    walk(0,1)
    return frozenset(sum(1<<(v^origin) for v in bits(cycle))
                     for cycle in rooted for origin in range(32))


@lru_cache(maxsize=1)
def forbidden_diagram():
    nodes=[]
    unique={}

    @lru_cache(None)
    def build(index,family):
        if not family:
            return 0
        if not family[0]:
            return 1
        mask=1<<index
        low=build(index+1,tuple(x for x in family if not x&mask))
        high=build(index+1,tuple(x^mask for x in family if x&mask))
        if not high:
            return low
        key=(index,low,high)
        if key not in unique:
            unique[key]=len(nodes)+2
            nodes.append(key)
        return unique[key]

    return build(0,tuple(sorted(long_cycles()))),nodes


def encode_long_cycles(formula,pool,vertices):
    root,nodes=forbidden_diagram()
    truth=pool.id()
    formula.append([truth])
    # A safety indicator means no forbidden subset is fully selected.
    safe=[truth,-truth]
    for index,low,high in nodes:
        variable=pool.id()
        formula.extend([[-variable,safe[low]],
                        [-variable,-vertices[index],safe[high]]])
        safe.append(variable)
    formula.append([safe[root]])


def add_long_cycle_tilings(formula,pool,tilings=((0,1,2,3,4),(2,3,5,7,8))):
    for axes in tilings:
        offsets=[sum(1<<axis for i,axis in enumerate(axes) if label>>i&1)
                 for label in range(32)]
        free=offsets[-1]
        for origin in range(512):
            if not origin&free:
                encode_long_cycles(formula,pool,[origin+v+1 for v in offsets])
    return 16*len(tilings)
