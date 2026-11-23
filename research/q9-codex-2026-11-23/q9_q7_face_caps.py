"""Connect Q7 linear-forest caps to every pair of fixed coordinates."""

from itertools import combinations

from q9_direction_frequency import append_upper_bound
from q9_overlapping_cross18 import value_literals
from q9_square_census import add_popcount
from verify_q9_free_dimension_cuts import edge7


def threshold(formula, pool, bits, minimum):
    active = pool.id()
    append_upper_bound(formula, bits, minimum-1, [active])
    append_upper_bound(formula, [-bit for bit in bits], (1<<len(bits))-1-minimum, [-active])
    return active


def add_contact_cuts(formula, pool, contacts, states):
    for (a, b), bonds in contacts.items():
        cross = add_popcount(formula, pool, [bonds[:]])
        positive = threshold(formula, pool, cross, 1)
        at_least_four = threshold(formula, pool, cross, 4)
        for first, second in ((a,b),(b,a)):
            v,c = states[first]
            anchor = [-lit for lit in value_literals(v,56)+value_literals(c,4)]
            v,c = states[second]
            for size in (4,5):
                guard = anchor + [-lit for lit in value_literals(c,size)]
                at_least_51 = threshold(formula, pool, v, 51+size)
                formula.append([*guard,-positive,-at_least_51])
            for size in (4,5,6):
                guard = anchor + [-lit for lit in value_literals(c,size)]
                at_least_50 = threshold(formula, pool, v, 50+size)
                formula.append([*guard,-at_least_four,-at_least_50])


def terminal_marks(formula, pool, a, b, endpoint):
    flags=[]
    for v in (0,endpoint):
        first,second=(v^(1<<a))+1,(v^(1<<b))+1
        active=pool.id()
        formula.extend([[-first,active],[-second,active],[-active,first,second]])
        flags.append(active)
    return flags


def terminal_vertex_cap(components, isolated):
    assert 0<=isolated<=components
    return min(64,edge7(components-isolated)+components)


def add_q7_face_caps(formula, pool, bonds, endpoint, contact_cuts=False, terminal_isolates=False):
    truth = pool.id()
    formula.append([truth])
    for a, b in combinations(range(9), 2):
        face_mask = (1 << a) | (1 << b)
        marks=terminal_marks(formula,pool,a,b,endpoint) if terminal_isolates else ()
        faces = (0, 1 << a, 1 << b, face_mask)
        incident = {v: [] for v in faces}
        contacts = {}
        states = {}
        axis_edges = {v: {} for v in faces}
        for u, v, used in bonds:
            first, second = u & face_mask, v & face_mask
            if first != second:
                incident[first].append(used)
                incident[second].append(used)
                if contact_cuts:
                    contacts.setdefault((first,second),[]).append(used)
            else:
                axis = u ^ v
                axis_edges[first].setdefault(axis, []).append(used)
        for face in faces:
            occupied = [v+1 for v in range(512) if v & face_mask == face]
            vertices = add_popcount(formula, pool, [occupied])
            terminals = int(face == 0) + int(face == (endpoint & face_mask))
            incidence = add_popcount(formula, pool, [incident[face]+[truth]*terminals])
            assert incidence[0] is not None
            formula.append([-incidence[0]])
            components = incidence[1:]
            states[face] = (vertices,components)
            append_upper_bound(formula, vertices, 64)
            for c in range(17):
                guard = [-lit for lit in value_literals(components, c)]
                append_upper_bound(formula, vertices, edge7(c)+c, guard)
                present = [marker for v,marker in zip((0,endpoint),marks) if v&face_mask==face]
                for isolated in range(1,len(present)+1):
                    if c<isolated:
                        for chosen in combinations(present,isolated):
                            formula.append([*guard,*(-flag for flag in chosen)])
                        continue
                    cap=terminal_vertex_cap(c,isolated)
                    if cap<terminal_vertex_cap(c,0):
                        for chosen in combinations(present,isolated):
                            append_upper_bound(formula,vertices,cap,
                                               [*guard,*(-flag for flag in chosen)])

            # Appendix D.2: every 52-edge Q7 forest has four components
            # and at least one coordinate direction with no internal edge.
            guard = [-lit for lit in value_literals(components, 4)]
            guard.extend(-lit for lit in value_literals(vertices, 56))
            unused = []
            for used_in_axis in axis_edges[face].values():
                flag = pool.id()
                unused.append(flag)
                formula.extend([[-flag,-used] for used in used_in_axis])
            formula.append([*guard,*unused])
        if contact_cuts:
            add_contact_cuts(formula, pool, contacts, states)
