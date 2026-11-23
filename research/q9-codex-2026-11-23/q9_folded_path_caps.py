"""Constraints on antipodal pairs of vertices in an induced Q9 path."""

from collections import defaultdict
from itertools import combinations

from pysat.formula import IDPool


def add_folded_caps(formula, limits, endpoint, physical=None):
    pool=IDPool(start_from=max(formula.nv,max(abs(lit) for bank,_ in limits for lit in bank))+1)
    present=[]
    double=[]
    for v in range(256):
        a,b=v+1,(v^511)+1
        p,d=pool.id(),pool.id()
        formula.extend([[-a,p],[-b,p],[-p,a,b],[-d,a],[-d,b],[d,-a,-b]])
        present.append(p)
        double.append(d)

    def guarded_at_most(lits, upper, condition):
        slack=len(lits)-upper
        if slack<=0:
            return
        guards=[condition]
        for _ in range(slack-1):
            guard=pool.id()
            guards.append(guard)
            formula.extend([[-guard,condition],[guard,-condition]])
        limits.append((lits+guards,len(lits)))

    generators=tuple(1<<i for i in range(8))+(255,)
    for v in range(256):
        neighbors=[v^axis for axis in generators]
        terminals=int(v==0)+int(v==min(endpoint,endpoint^511))
        # Each doubled neighbour contributes an edge to either selected sheet.
        guarded_at_most([double[w] for w in neighbors],1 if terminals else 2,present[v])
        weighted=[lit for w in neighbors for lit in (present[w],double[w])]
        degree_sum=4-terminals
        guarded_at_most(weighted,degree_sum,double[v])
        guarded_at_most([-lit for lit in weighted],len(weighted)-degree_sum,double[v])
        for a,b in combinations(generators,2):
            square=(v,v^a,v^b,v^a^b)
            if v==min(square):
                # Selecting both sheets over an entire quotient cycle
                # contains a cycle in the full cube.
                formula.append([-double[w] for w in square])
    if physical is not None:
        add_quotient_topology(formula,pool,present,double,physical,generators)


def add_quotient_topology(formula,pool,present,double,physical,generators):
    from q9_count_lex import equality,lex_leader
    from q9_q4_tiling_connectivity import require_quotient_connected

    def orbit(v):
        return min(v,v^511)

    borders=defaultdict(list)
    for a,b,edge in physical:
        borders[tuple(sorted((orbit(a),orbit(b))))].append(edge)
    assert len(borders)==256*9//2 and all(len(edges)==2 for edges in borders.values())
    require_quotient_connected(formula,pool,dict(enumerate(present)),borders,0)

    ranks=[[pool.id() for _ in range(8)] for _ in double]
    predecessors=[[] for _ in double]
    for a,b in borders:
        same=equality(formula,pool,ranks[a],ranks[b])
        for source,target in ((a,b),(b,a)):
            parent=pool.id()
            predecessors[target].append(parent)
            formula.extend([[-parent,double[source]],[-parent,double[target]],[-parent,-same]])
            lex_leader(formula,pool,list(zip(ranks[source],ranks[target])),[-parent])
    # A cycle of doubled pairs would lift to one or two fully selected cycles.
    # In a forest, an interior doubled pair can point toward a leaf.
    for v,doubled in enumerate(double):
        for a,b in combinations((v^mask for mask in generators),2):
            formula.append([-doubled,-double[a],-double[b],*predecessors[v]])
