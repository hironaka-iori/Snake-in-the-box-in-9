"""Use every three-axis projection as a necessary connected walk."""

from itertools import combinations

from pysat.card import CardEnc, EncType


def interface_flags(formula, pool, bonds):
    present, doubled = pool.id(), pool.id()
    formula.extend([[-edge,present] for edge in bonds])
    formula.append([-present,*bonds])
    formula.append([-doubled,present])
    at_least_two = CardEnc.atleast(bonds,2,vpool=pool,encoding=EncType.seqcounter)
    formula.extend([[-doubled,*clause] for clause in at_least_two.clauses])
    return present,doubled


def add_projection_connectivity(formula, pool, bonds, endpoint, vertex_count):
    layer_size = 32  # The selected path intersects Q6 in an induced linear forest.
    assert vertex_count > 4 * layer_size
    for axes in combinations(range(9),3):
        face_mask = sum(1<<axis for axis in axes)
        values = [sum((1<<axis) for i,axis in enumerate(axes) if label>>i&1)
                  for label in range(8)]
        face_id = {v:i for i,v in enumerate(values)}
        terminal = face_id[endpoint&face_mask]
        interfaces = {}
        for a,b,edge in bonds:
            first,second = face_id[a&face_mask],face_id[b&face_mask]
            if first!=second:
                interfaces.setdefault((first,second),[]).append(edge)
        flags = {interface:interface_flags(formula,pool,edges)
                 for interface,edges in interfaces.items()}
        occupied = [pool.id() for _ in values]
        for v in range(512):
            formula.append([-v-1,occupied[face_id[v&face_mask]]])
        for side in range(1,255):
            size = side.bit_count()
            if size>4 or (size==4 and side>(255 ^ side)):
                continue
            selected_interfaces = [flag for (a,b),flag in flags.items()
                                   if ((side>>a)^(side>>b))&1]
            present,doubled = map(list,zip(*selected_interfaces))
            # Outside is always occupied. Inside is forced by the same cap
            # whenever the complementary set of layers is too small.
            if vertex_count>(8-size)*layer_size:
                guard = []
            else:
                entered = pool.id()
                for f in range(8):
                    if side>>f&1:
                        formula.append([-occupied[f],entered])
                guard = [-entered]
            formula.append([*guard,*present])
            if bool(side&1)==bool(side>>terminal&1):
                for pivot in present:
                    formula.append([*guard,*doubled,*(p for p in present if p!=pivot)])
