"""Connect occupied layers in the five-coordinate quotient of a Q4 tiling."""

from q9_count_lex import equality, lex_leader


def require_quotient_connected(formula, pool, present, borders, root):
    width = max(1,(len(present)-1).bit_length())
    ranks = {layer:[pool.id() for _ in range(width)] for layer in present}
    parents = {layer:[] for layer in present}
    formula.extend([[present[root]], *[[-bit] for bit in ranks[root]]])
    for (a,b), connections in borders.items():
        if not connections:
            continue
        same = equality(formula,pool,ranks[a],ranks[b])
        for source,target in ((a,b),(b,a)):
            if target==root:
                continue
            witness = pool.id()
            formula.extend([[-witness,present[source]],[-witness,present[target]],
                            [-witness,*connections],[-witness,-same]])
            pairs = list(zip(reversed(ranks[source]),reversed(ranks[target])))
            lex_leader(formula,pool,pairs,[-witness])
            parents[target].append(witness)
    for layer,flag in present.items():
        if layer!=root:
            formula.append([-flag,*parents[layer]])


def add_tiling_connectivity(formula,pool,bonds,axes):
    free = sum(1<<axis for axis in axes)
    present = {}
    for u in range(512):
        layer = u&~free
        if layer not in present:
            present[layer] = pool.id()
        formula.append([-u-1,present[layer]])
    borders = {}
    for a,b,edge in bonds:
        first,second = a&~free,b&~free
        if first!=second:
            borders.setdefault((first,second),[]).append(edge)
    require_quotient_connected(formula,pool,present,borders,0)
