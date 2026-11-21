# Milestone 42: inductive inequalities a(n) <= 2 a(n-1) - f (facet split)

**No bound is claimed. Result: dead end for n = 9 below 229 by hand-checkable arguments.**
Numbers below are SAT evidence (CaDiCaL via python-sat, lazy cycle cuts) unless marked.

## 1. The inductive form of the facet split (complete written proof, milestone 22/39)

Cut a snake of Q_n along its least-crossed direction (k <= floor(a(n)/n) crossings). The halves
are induced linear forests of Q_{n-1} with c0 + c1 = k + 1 paths, so

    a(n) + 1 <= g_{n-1}(c0) + g_{n-1}(c1),   i.e.   a(n) <= 2 a(n-1) + 1 + E(c0) + E(c1),

with the forest excess E(c) = g_{n-1}(c) - g_{n-1}(1) = g_{n-1}(c) - a(n-1) - 1.
This is exactly an inequality "a(n) <= 2 a(n-1) - f": f = -(1 + E(c0) + E(c1)).
- Truth satisfies a(n) <= 2 a(n-1) for n <= 8 (13=2*7-1, 26=2*13, 50=2*26-2, 98=2*50-2), but
  the excess is positive and grows: E5(3)=1, E6(5)=2, E7(7) >= 5, E8(13) >= 13 (forests of 112
  vertices with <= 13 paths; milestone 29 annealing, validated witnesses).
- So the inductive form cannot beat a(9) <= 2*98 + 1 + 26 = 223, and any bound from it needs
  the value g8(13), which has no short proof (milestone 32: LP/flag relaxations fail; the sibling
  milestone 39 attacks it by cube-and-conquer). Calibration (milestone 29): 28 / 56 / 113 edges
  for n = 6 / 7 / 8 against the truth 26 / 50 / 98.
- Recursing g itself (split the forest again) gives Huang-level values (milestone 29 section 4);
  averaging over all directions or over Q7/Q6 subcubes is never better than the least-crossed
  direction for monotone g, and the subcube versions hit the locality ceilings of milestone 41.

## 2. Coupling the two halves (`scripts/coupled.py`, new; SAT evidence)

Extra necessary conditions: A, B share exactly the crossing points (|A & B| <= k), each crossing
point is an endpoint in both halves, and there are <= 2 free path-ends in total. Max |A|+|B|:

| split | k | uncoupled sum of g | coupled | truth (vertices) |
|---|---|---|---|---|
| Q5 -> Q6 | <= 4 | 29 | **28** (UNSAT at 29) | 27 |
| Q6 -> Q7 | <= 7 | 57 | **>= 56** (SAT, 56 at k = 7) | 51 |

Coupling gains at most one vertex per step (Q7: 56 edges -> >= 55, truth 50). The gap to the
truth (6 in Q7) is in the global single-path structure, not in the facet interaction. Lifted
to Q9 it would also need a joint Q8 SAT harder than milestone 39's single-facet problem.
**Dead end.**

## 3. Literature recursive bounds
Douglas (1969), Deimer (1985), Solov'eva (1987), Snevily (1994: 2^(n-1)(1 - 1/(20n-41)), n >= 12),
Zemor (1997: 2^(n-1)(1 - Theta(1/sqrt n))). All are 2^(n-1) minus a vanishing fraction; at
n = 9 they are all >= ~250 edges, far above the proved 231. Exact small data does not repair
them: their recursions are of the facet/neighbourhood type above.

## Conclusion
Every inductive inequality of facet type reduces to the Q8 forest excess E8(13), which is >= 13
and only accessible by large SAT computations (milestone 39). No hand-checkable inequality below
229 was found; the route floor is 223 (2*112 - 1).

Logs: `data/coupled_n6_K7.log`, `data/coupled_n6_K8.log` (runs stopped by the 3500 s timeout
while searching 57 vertices). Q5 runs: `python3 scripts/coupled.py 5 K coupled 20` (seconds).
