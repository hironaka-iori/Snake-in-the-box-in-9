"""Lower bounds on the value of any moment / Lasserre / k-point SDP relaxation for snakes in Q9 whose
constraints each involve at most d vertices.

A 0/1 point X in {0,1}^Q9 is feasible for such a relaxation (its point-mass moment vector satisfies
every PSD and localising condition) as soon as X satisfies each imposed constraint.  The natural
constraints of the snake problem are: induced degree <= 2, no induced cycle on <= d vertices (a cycle
on j vertices is a degree-j monomial), and the endpoint identity sum_v x_v (2 - deg(v)) = 2 (degree 2).
So a set X with those properties that is a disjoint union of induced cycles of length > d plus one
induced path gives a feasible point with objective |X| - 1 edges... (objective m = |X| - 1 for a path).

This script builds and checks three such sets:
  X256: 2^(n-4) disjoint induced 8-cycles (C in Q4 and its translate C + 0101 alternating over the
        bipartition of Q5) minus one vertex (milestone 32, section 5);
  X224: milestone 11's adversary224 (16 disjoint induced 14-cycles) minus one vertex;
  X208: milestone 11's adversary208 (8 disjoint induced 26-cycles) minus one vertex.
It prints, for each: |X|, the cycle lengths of the full union, max induced degree, the endpoint sum
after deleting a vertex, and the SDP ceiling m >= |X| - 2 that follows for d < shortest cycle.
It also prints the rough number of B9-orbits of d-subsets (C(512,d)/|B9|), the size of the symmetry
reduced variable set of a level d/2 moment relaxation."""
import json, os, math
from itertools import combinations
n = 9; V = 1 << n
HERE = os.path.dirname(os.path.abspath(__file__))
M11 = os.path.join(HERE, '..', '..', '11-local-ceiling', 'data')

def comps(S):
    S = set(S); seen = set(); out = []
    for u in S:
        if u in seen: continue
        st = [u]; seen.add(u); c = []
        while st:
            x = st.pop(); c.append(x)
            for i in range(n):
                y = x ^ (1 << i)
                if y in S and y not in seen: seen.add(y); st.append(y)
        out.append(c)
    return out

def info(S):
    S = set(S)
    deg = {x: sum(1 for i in range(n) if x ^ (1 << i) in S) for x in S}
    cl = sorted(len(c) for c in comps(S))
    two_reg = all(d == 2 for d in deg.values())
    return max(deg.values()), two_reg, cl

def x256():
    # induced 8-cycle in Q4
    C = None
    for cyc in [[0, 1, 3, 7, 15, 14, 12, 8]]:
        C = cyc
    Cs = set(C); Cp = {x ^ 0b0101 for x in C}
    assert not (Cs & Cp)
    S = []
    for y in range(1 << (n - 4)):
        part = Cs if bin(y).count('1') % 2 == 0 else Cp
        S += [x | (y << 4) for x in part]
    return S

sets = {'X256': x256(),
        'X224': json.load(open(os.path.join(M11, 'adversary224.json')))['S'],
        'X208': json.load(open(os.path.join(M11, 'adversary208.json')))['S']}
B9 = 2 ** 9 * math.factorial(9)
out = {}
for name, S in sets.items():
    md, reg, cl = info(S)
    T = set(S); T.discard(min(T))
    deg = {x: sum(1 for i in range(n) if x ^ (1 << i) in T) for x in T}
    endsum = sum(2 - d for d in deg.values())
    g = min(cl)
    rec = dict(set=name, vertices=len(S), two_regular=reg, max_deg=md, cycle_lengths=sorted(set(cl)), ncycles=len(cl),
               after_deleting_one_vertex=dict(vertices=len(T), endpoint_sum=endsum),
               sdp_value_at_least_edges=len(T) - 1, valid_for_constraint_support_below=g)
    out[name] = rec
    print(rec)
for d in (4, 6, 8, 12, 14, 26):
    print('d = %2d: C(512,d)/|B9| = %.2e' % (d, math.comb(V, d) / B9))
json.dump(out, open(os.path.join(HERE, '..', 'data', 'sdp_ceiling.json'), 'w'), indent=1)
