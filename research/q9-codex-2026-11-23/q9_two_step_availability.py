"""Two-step continuation constraints using each colour's induced footprint."""

from itertools import combinations

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

from q9_overlapping_cross18 import value_literals
from q9_square_census import add_popcount


def add_ball_connectivity(formula, pool, graph, dim, required):
    n = 1 << dim
    for centre in range(n):
        shell = [centre ^ (1 << a) ^ (1 << b)
                 for a,b in combinations(range(dim),2)]
        inside = {centre, *shell}
        boundary = [edge for u in shell for v,edge in graph[u] if v not in inside]
        crossed = pool.id()
        formula.append([-crossed,*boundary])
        colour = centre.bit_count()%2
        if len(inside)<required[colour]:
            for u in sorted(inside):
                formula.append([-u-1,crossed])
        else:
            outside = [u for u in range(n) if u not in inside and u.bit_count()%2==colour]
            occupied = pool.id()
            for u in sorted(inside):
                formula.append([-u-1,occupied])
            for u in outside:
                formula.append([-occupied,-u-1,crossed])


def add_exact_degrees(formula,pool,dim,endpoints):
    n = 1 << dim
    eligible = []
    for v in range(n):
        neighbors = [(v ^ (1 << i))+1 for i in range(dim)]
        degree = add_popcount(formula, pool, [neighbors])
        target = 1 if v in endpoints else 2
        equal = value_literals(degree,target)
        candidate = pool.id()
        formula.extend([[-candidate, lit] for lit in equal])
        formula.append([candidate, *(-lit for lit in equal)])
        formula.append([-v-1,candidate])
        eligible.append(candidate)
    return eligible


def add_two_step_availability(formula, dim, endpoints, length, ball_cuts=False):
    n = 1 << dim
    pool = IDPool(start_from=formula.nv+1)
    end_a, end_b = endpoints
    eligible = add_exact_degrees(formula,pool,dim,endpoints)
    colours = [[candidate for v,candidate in enumerate(eligible) if v.bit_count()%2==colour]
               for colour in (0,1)]
    required = [(length+2-(colour^(end_a.bit_count()%2)))//2 for colour in (0,1)]
    for colour, bank in enumerate(colours):
        formula.extend(CardEnc.atleast(bank,required[colour],vpool=pool,
                                       encoding=EncType.cardnetwrk).clauses)

    destinations = [[] for _ in range(n)]
    graph = [[] for _ in range(n)] if ball_cuts else None
    for a,b in combinations((1 << i for i in range(dim)),2):
        mask = a | b
        for u in range(n):
            v = u ^ mask
            if v <= u:
                continue
            first,second = eligible[u ^ a],eligible[u ^ b]
            edge = pool.id()
            formula.extend([[-edge,u+1],[-edge,v+1],[-edge,first,second],
                            [-u-1,-v-1,-first,edge],[-u-1,-v-1,-second,edge]])
            destinations[u].append(edge)
            destinations[v].append(edge)
            if graph is not None:
                graph[u].append((v,edge))
                graph[v].append((u,edge))
    for v, candidates in enumerate(destinations):
        for endpoint in (end_a,end_b):
            if (v ^ endpoint).bit_count()==1:
                candidates.append(eligible[endpoint])
        needed = 1 if v in endpoints else 2
        if len(candidates)<needed:
            formula.append([-v-1])
            continue
        # Guard the at-least constraint only, leaving its auxiliary variables
        # unrestricted when v is absent.
        clauses = CardEnc.atleast(candidates,needed,vpool=pool,
                                 encoding=EncType.seqcounter).clauses
        formula.extend([[-v-1,*clause] for clause in clauses])

    if graph is not None:
        add_ball_connectivity(formula,pool,graph,dim,required)
