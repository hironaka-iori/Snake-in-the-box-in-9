"""Exact masks for the Q3 face spanned by distance-three endpoints."""

from itertools import permutations

from q9_direction_frequency import append_order
from verify_q9_free_dimension_cuts import deg, parts

MASKS = (129,131,153)


def canonical(mask):
    points = [v for v in range(8) if mask>>v&1]
    return min(sum(1<<(flip^sum(((v>>axis)&1)<<i for i,axis in enumerate(order)))
                   for v in points) for order in permutations(range(3)) for flip in (0,7))


def audit():
    admissible={}
    for mask in range(256):
        if mask&129!=129:
            continue
        points={v for v in range(8) if mask>>v&1}
        if any(deg(points,v,3)>(1 if v in (0,7) else 2) for v in points):
            continue
        if any({0,7}<=part or all(deg(part,v,3)==2 for v in part)
               for part in parts(points,3)):
            continue
        admissible[mask]=canonical(mask)
    simple={129}
    for axis in range(3):
        neighbor=1<<axis
        a,b=1<<neighbor,1<<(7^neighbor)
        simple.update((129|a,129|b,129|a|b))
    assert set(admissible)==simple and set(admissible.values())==set(MASKS)
    return admissible


def constrain(formula,pool,counts,mask):
    assert mask in MASKS
    formula.extend([v+1 if mask>>v&1 else -v-1] for v in range(8))
    order_pairs=[(a,a+1) for a in range(3,8)]
    if mask==129:
        order_pairs.extend(((0,1),(1,2)))
    elif mask==131:
        order_pairs.append((1,2))
    else:
        order_pairs.append((0,1))
    for a,b in order_pairs:
        append_order(formula,pool,counts[a],counts[b])
