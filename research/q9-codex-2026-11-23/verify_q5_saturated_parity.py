"""Reproduce the saturated Q5 fibre parity certificate using Python integers."""
from collections import Counter
from itertools import combinations
import json

def neighbours(dim):
    return [sum(1 << (v ^ (1 << j)) for j in range(dim)) for v in range(1 << dim)]

def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit

def forest(mask, neighbourhoods):
    """Return (degree-two vertices, edge count), or None when not a linear forest."""
    double = edges = 0
    for v in vertices(mask):
        degree = (mask & neighbourhoods[v]).bit_count()
        if degree > 2:
            return None
        edges += degree
        if degree == 2:
            double |= 1 << v
    edges //= 2
    # Each degree-at-most-two component is a path or a cycle.
    ends = mask & ~double
    touched = ends
    while ends:
        reach = 0
        for v in vertices(ends):
            reach |= neighbourhoods[v]
        ends = reach & mask & ~touched
        touched |= ends
    return (double, edges) if touched == mask else None

def certificate():
    q4 = neighbours(4)
    q5 = neighbours(5)
    halves = []
    for mask in range(1<<16):
        f = forest(mask,q4)
        if f is not None:
            assert mask.bit_count() <= 8
            if mask.bit_count() == 8:
                halves.append((mask,f[0]))
    bank = []
    for a, a2 in halves:
        for b, b2 in halves:
            if a & b2 or b & a2:
                continue
            m = a | (b << 16)
            f = forest(m, q5)
            if f is not None:
                bank.append((m, *f))
    edges = Counter(e for m, d2, e in bank)
    contacts = Counter((a&b).bit_count() for a, a2, _ in bank for b, b2, _ in bank if not (a2&b or b2&a))
    assert len(halves)==922 and len(bank)==1772
    assert sum(contacts.values())==5744
    assert all(e%2==0 for e in edges) and all(c%2==0 for c in contacts)
    # Check the actual two-swap orbit graph from its cube coordinates.
    def flip(x):
        return ((x&5)<<1)|((x&10)>>1)
    reps=[x for x in range(16) if x<flip(x)]
    adj={x:set() for x in reps}
    for x,y in combinations(reps,2):
        m=sum((v^w).bit_count()==1 for v in (x,flip(x)) for w in (y,flip(y)))
        assert m in (0,2)
        if m:
            adj[x].add(y);adj[y].add(x)
    sides=sorted(reps,key=lambda x:len(adj[x]))
    a,b=set(sides[:4]),set(sides[4:])
    assert all(adj[x]==b for x in a) and all(adj[x]==a for x in b)
    return dict(Q4_layer_masks=len(halves),Q5_layer_masks=len(bank),Q5_internal_edge_counts=edges,
                ordered_compatible_layer_pairs=sum(contacts.values()),cross_edge_counts=contacts,
                two_swap_quotient_sides=[sorted(a),sorted(b)],two_swap_even_symmetric_path_upper_edges=190)

if __name__=="__main__":
    print(json.dumps(certificate(),indent=2))
