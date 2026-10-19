# Dense induced cycle unions with long cycles (search E2, 19 October 2026)

The local-window ceiling of this milestone comes from *adversaries*: sets of Q9 vertices
inducing a 2-regular subgraph (disjoint induced cycles, no edges between them).  A window
that never sees a whole cycle cannot tell such a set from a snake, so an adversary with
v vertices caps any such method near v - 1 edges.  adv208 has 8 cycles of length 26 and
adv224 has 16 of length 14.  The question here: do dense adversaries exist whose cycles
are all long (length >= g)?  If one with v >= 198 existed for some g, no window method
that cannot see a whole cycle of length g could reach 196.

## Result

No hit.  The best set found has **v = 176** with all cycles long, for every g tried:

| g | best v | cycles | file (`data/long_girth/`) |
|---|---|---|---|
| 28, 32, 40 | 176 | 4 x 44 | `four_44_cycles_176.json` |
| 48 | 176 | 2 x 88 | `two_88_cycles_176.json` |
| 28 (Q7 x Q2 fibres) | 160 | 4 x 40 | `fibre_q7q2_g28_160.json` |

`scripts/long_girth/verify.py FILE...` checks each set from its vertex list (induced degree
exactly 2 everywhere, edges = vertices, cycle lengths); it also accepts adv208 and adv224.
A search that finds nothing proves nothing: these are not upper bounds on such sets.

Densities: 14-cycles 0.4375 (adv224), 26-cycles 0.406 (adv208), best found with cycles
>= 28: 0.344; v = 198 needs 0.387.  Every structured search stalled at 176 (the next
targets, 180/184, ended "unknown within the conflict budget", never UNSAT).  This
suggests, without proof, a threshold near g = 27-28 above which cycle-union adversaries
stop blocking 196.

## Methods (`scripts/long_girth/`)

1. `sat2reg.py`: exact SAT encoding (pysat CaDiCaL).  Every chosen vertex has one in- and
   one out-edge, edges between chosen vertices are oriented, labels count steps along a
   cycle (bounded by 2g - 2), and each cycle needs a reset vertex whose predecessor has
   label >= g - 1; this forces every cycle to have length >= g without lazy cuts.  On
   Q7 x Q2 fibres it found |A| + |B| = 80 (v = 160) in 9 s; 88 and 99 did not finish.
2. `packn.c`, `q7pack.c`: randomized ruin-and-recreate packing of induced cycles; best
   140 (g = 28) and 134 (g = 48) directly in Q9.
3. `quot.py`, `quotl.py`: translation-symmetric SAT.  S is a union of cosets of a random
   binary code T of dimension k and minimum weight >= 3; the search runs on the quotient
   Cayley graph (induced degree is preserved; a quotient cycle of length L lifts to cycles
   of length L or 2L).  This gave all the 176 sets (k = 3 and k = 2).

## A rigorous side result for Q7 x Q2 fibres

A set of maximum induced degree 2 in Q_n has at most n 2^n / (2n - 2) vertices (74 in
Q7).  For g >= 40 a Q7 layer holds at most one cycle (two would need >= 80 > 74 vertices),
and an induced cycle of Q7 has length at most 48 (known value, not recomputed), so
|A| + |B| <= 96 < 99: **for g >= 40 the Q7 x Q2 fibre construction cannot reach 198.**
Q6 x Q3 fibres cap cycle length at 26, so they cannot reach g >= 28 at all.
