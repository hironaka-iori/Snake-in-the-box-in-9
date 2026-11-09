# A local density LP for induced linear forests in Q_n

Run of 9 November 2026, one core at nice 10. Status: **negative for the LP; one positive side
result** (see §5). Nothing here is a Lean theorem, and no bound on a(9) changes.

## Question

Milestone 29 reduced a(9) ≤ 223 to g8(13) ≤ 112, and a(9) ≤ 233 to g8(c) ≤ 117 for c ≤ 14.
Here g_n(c) is the largest induced linear forest of Q_n with at most c paths. The idea tested
here: acyclicity and maximum degree 2 are local conditions, and the number of paths is the only
global one. So a flag-algebra-style averaging LP over labelled subcube patterns should bound
|F| in terms of c, with a dual certificate that Lean could check by enumerating patterns.

## 1. The LP (`scripts/patterns.py`, `scripts/forestlp.py`, `scripts/taglp.py`)

Fix k (here k = 4). A **labelled pattern** of a k-subcube Q is F ∩ Q together with the global
degree l(v) ∈ {0,1,2} of each v ∈ F ∩ Q. A pattern is **valid** when the following hold:
- F ∩ Q induces a linear forest in Q_k;
- deg_Q(v) ≤ l(v) ≤ 2;
- the out-degrees l − deg_Q can be realised by direction sets on the n − k outside directions,
  with adjacent vertices never sharing one (otherwise there is a 4-cycle).

Q4 has 14 911 induced linear forests, 102 up to symmetry, and 2968 labelled patterns up to B_4.
The variable x_τ is the fraction of the C(n,k)·2^(n−k) subcubes of type τ.

Every one of the following is an identity or inequality for **every** induced linear forest with
at most c paths:

1. Σ x_τ = 1.
2. |F|/2^n = Σ x_τ |A_τ|/2^k (the objective).
3. Σ x_τ e_τ/2^k ≤ 2c/2^n, where e_τ = Σ_v (2 − l(v)), because Σ_F (2 − deg) = 2·#paths.
4. **Face consistency, for every j < k (hypergeometric version, `forestlp.py`).** Take any
   labelled j-pattern σ, any position p in it and any γ ∈ {0,1,2}. A vertex with o F-neighbours
   outside a j-face R gains exactly γ of them in exactly C(o,γ)·C(n−j−o, k−j−γ) of the
   C(n−j, k−j) k-subcubes that contain R. Summing over the pairs R ⊂ Q gives a linear equation.
5. **Tagged version (`taglp.py`, Sherali–Adams marginals).** Each out-vertex records *which*
   outside directions it uses, up to B_k × S_{n−k}. Each j-face R, rooted at the k − j directions
   of Q that R does not span, must occur equally often per orbit of rooted types. A rooted type
   that no valid pattern produces forces its unrooted type to have frequency 0. This subsumes (4).

Any dual vector (y, y_E ≥ 0) gives a rigorous bound:

    |F|/2^n ≤ max_τ [ |A_τ|/2^k − y_E e_τ/2^k − Σ_r y_r M_rτ ] + y_E · 2c/2^n.

`certify` evaluates this exactly over the rationals, with the duals rounded to denominators of
at most 10^6. So every bound reported below is exact, not a floating-point value.

## 2. A barrier that no LP of this kind can pass (rigorous)

The constant c enters only through the right-hand side of (3). The optimum of an LP as a function
of one right-hand side is **concave**. Each actual forest is a feasible point. So the LP bound
B(c) is at least the concave majorant of the true function c ↦ g8(c), and therefore at least the
concave majorant of the known lower bounds:
- 99 at c = 1;
- 104 at c = 4;
- 112 for c = 8–16;
- 96 + c for c = 16–32, reaching 128 at c = 32.

Between (8, 112) and (32, 128) the slope is 2/3. Hence

    B(13) ≥ 115.33,   B(14) ≥ 116.

- **Any c-linear relaxation (this LP, any larger k, any added local constraints, flag-algebra
  quadratic constraints with c in the right-hand side) cannot prove g8(13) ≤ 112.** The 223 route
  is closed for this method.
- Feeding the concave-majorant values (floored) into `layer.py`'s `bound1` gives **a(9) ≤ 229 as
  the best conceivable outcome**. It needs an LP that is exact up to the concave hull.
- The 233 target (g8(c) ≤ 117 for c ≤ 14) leaves a margin of only 1–2 vertices over the hull.

The plateau g_n(c) = 7·2^(n−4) on c ∈ [2^(n−5), 2^(n−4)] is flat and then rises with slope 1.
That shape is exactly what concave relaxations miss: from the plateau to Huang's 2^(n−1) at
c = 2^(n−3), the plateau's right end lies strictly below the chord.

## 3. Calibration and results for k = 4 (`scripts/run_lp.py`, data in `data/lp_k4.jsonl`)

Every entry below is an exact rational bound, floored. "hyper" is the LP with (1)–(4) for all
j ≤ 3, "tagged" is the LP with (5). The hull column is the concave majorant of the true values,
which is the best any such LP could do (§2).

| n | c | g_n(c) | hull | hyper | tagged |
|---|---|---|---|---|---|
| 5 | 1 | 14 | 14.0 | 15 (15.33) | 15 (15.33) |
| 5 | 2 | 14 | 14.67 | 15 (15.67) | 15 (15.67) |
| 5 | 3 | 15 | 15.33 | 16 | 16 |
| 5 | 4 | 16 | 16 | 16 | 16 |
| 6 | 1 | 27 | 27 | 30 (30.53) | 30 (30.01) |
| 6 | 2 | 28 | 28.67 | 30 (30.85) | 30 (30.36) |
| 6 | 4 | 28 | 29.33 | 31 (31.46) | 30 (30.96) |
| 6 | 6 | 30 | 30.67 | 31 (31.94) | 31 (31.51) |
| 6 | 8 | 32 | 32 | 32 | 32 |
| 7 | 1 | 51 (exact: snake) | | 62 (62.19) | TAG7_1 |
| 7 | 4 | 56–57 | | 62 (62.76) | TAG7_4 |
| 7 | 8 | 56–57 | | 63 (63.48) | TAG7_8 |
| 8 | 8 | ≥ 112 | ≥ 112 | 126 (126.40) | not run |
| 8 | 13 | ≥ 112 | ≥ 115.33 | 127 (127.10) | not run |
| 8 | 14 | ≥ 112, ≤ 121 | ≥ 116 | 127 (127.21) | not run |
| 8 | 16 | ≥ 112 | ≥ 117.33 | 127 (127.44) | not run |
| 8 | 32 | 128 | 128 | 128 | not run |

- **The bounds are valid.** No bound undercuts a known value. It cannot: every forest, and even
  every set in §5, is a feasible point.
- **For g8 they are useless.** The hyper LP gives 126–127 for c = 8–16, against Huang's 128.
- **Implied a(9) bound.** With these g8 values, `layer.py`'s `bound1` gives a(9) ≤ 253 on its
  own. With the Lean bound 235 it gives 235, so nothing improves. Adding milestone 29's SAT bound
  g8(14) ≤ 121 does not help either.
- **Only the facet level does any work.**
  - With vertex-level consistency alone (j = 0, which is also the only level that is cheap for
    k = 5), the LP gives exactly 2^(n−1) for every c and n = 5, 6, 8.
  - With j ≤ 1 it gives the same.
  - j = 2 gains a few tenths. Everything else comes from j = 3.
- **Tagging the outside directions helps only a little.** At n = 6, c = 4 it gains 0.5 (31.46 to
  30.96). At n = 5 it gains nothing.
- **The ratio k/n decides how strong the LP is.**
  - At n = 5 the LP is the k = n − 1 case, and it is still 1.33 above the hull at c = 1.
  - At n = 8 a k-subcube sees a vertex's two F-neighbours only with probability
    C(n−2,k−2)/C(n,k) = C(6,2)/C(8,4) = 15/70.
  - A k = 5 LP at n = 8 has k/n = 0.625, below n = 6 with k = 4 (0.67), and that LP is 3 above
    the truth.

## 4. Why k = 5 was not run

Q5 has 64 233 113 induced linear forests, which `count5.c` counts in 10 minutes. That gives about
6.3·10^10 labelled patterns, roughly 1.6·10^7 orbits under B_5.
- The facet rows are the only useful ones (§3). With them the LP cannot be priced separably.
- The column generation would need an exhaustive pricing over Q5 patterns, about 10^3 core-seconds
  per round, over many rounds.
- The calibration says it would not come close in any case. At n = 8, k = 5 is a weaker window
  than k = 4 at n = 6, and that LP gives 31 for g6(4) = 28.

## 5. Side result: the plateau is a local phenomenon (`scripts/fake_sa.c`, `scripts/fakesat.py`)

To tell the weakness of the relaxation apart from the weakness of locality, consider
**locally forest-like sets**:
- induced subgraphs of Q_n with maximum degree ≤ 2;
- at most c path components;
- no cycle inside any k-subcube, so cycles that span more than k directions are allowed.

Write h_{n,k}(c) for their maximum size.
- Every forest is such a set, so g_n(c) ≤ h_{n,k}(c).
- Every such set is a feasible point of the k-subcube LP, so h_{n,k}(c) ≤ LP_k.

Exact values by SAT (`fake_table.py`, `data/fake_table.jsonl`, each query ≤ 2 s):

| c | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|---|
| h_{5,4} | 14 | 14 | 15 | 16 | 16 | | | | |
| g5 | – | 14 | 14 | 15 | 16 | | | | |
| h_{6,4} | 28 | 28 | 28 | 28 | 28 | 29 | 30 | 31 | 32 |
| h_{6,5} | 26 | 27 | 28 | 28 | 28 | 29 | 30 | 31 | 32 |
| g6 | – | 27 | 28 | 28 | 28 | 29 | 30 | 31 | 32 |

In Q5 the relaxed sets exceed g5 by one at c = 2 and 3. The witnesses are a 12-cycle spanning 5 directions plus short paths (for example, c = 2 gives 12 + 1 + 2). From Q6 on they agree with g on the plateau.

Simulated annealing, which gives lower bounds only:
- h_{7,4}(c) ≥ 56 for every c = 0..8. That is the Q7 plateau value, and the c = 0 value is
  attained by long cycles.
- In Q8 it finds 112 at c = 13 for every k = 4..7, and nothing larger.
- With k = 3, where 8-cycles inside Q4 are allowed, SA immediately finds 128.

So **forbidding cycles inside 4-subcubes already produces the 7·2^(n−4) plateau** in Q6 (exactly, for c = 0..4),
and apparently in Q7 and Q8. The plateau is not caused by global acyclicity. It is caused by the
induced 8-cycles of Q4, which are 168 per 4-subcube. Without them a density-1/2 set exists:
take the 8-cycle C ⊂ Q4 and its complement C + 0101, which is also an induced 8-cycle, and
alternate them over the bipartition of Q_{n−4}. This gives 2^(n−4) disjoint 8-cycles, 2^(n−1)
vertices, all of degree 2. The LP's gap to the truth is therefore a gap of the relaxation, not of
locality.

Locality alone could in principle prove the plateau, which suggested trying the relaxation as an
easier SAT problem. It uses no lazy cuts and no level encoding: all cycles of span ≤ 4 are
excluded by clauses up front, with a valid P5 symmetry normalisation. For Q6 it is instant. For
the open Q7 query (c = 8, |F| ≥ 57, which would prove g7(8) = 56) it was **still unknown after
3680 s wall / 3040 s CPU** (`data/fakesat_q7.jsonl`). That is no better than milestone 29's
genuine-forest encoding, which was unknown after more than 2400 s.

## 6. Assessment

- **The 223 route is out of reach for every LP or flag-algebra relaxation that is linear in c.**
  The concave hull of the true g8 already forces a bound of at least 115.33 at c = 13. The best
  conceivable outcome is a(9) ≤ 229. It needs the LP to be within about 1 vertex of the hull at
  c = 8–16 and c = 32.
- **The k = 4 LP, hypergeometric or tagged, is far from that.**
  - Calibration: 15.33 / 30.5–31 / 62–63 for c around the plateau in Q5, Q6, Q7, against
    14 / 28 / 56.
  - In Q8: 126–127 for c = 8–16, which gives no new a(9) bound.
- **Larger windows do not help in practice.**
  - The useful constraints are facet marginals. Their strength is governed by k/n.
  - Even k = n − 1 at n = 5 stays 1.3 above the hull.
  - Q5 patterns (6·10^10 labelled) are beyond a full LP. Q6 and Q7 patterns are far beyond.
- **What survives:**
  1. The rigorous concavity barrier.
  2. The fact that the plateau is a local property: no induced C8 inside a Q4 plus degree ≤ 2
     already gives it in Q5 and Q6. A proof of the plateau should exploit the 8-cycles of Q4,
     which is a 4-local, finite structure. Note, though, that SAT does not find this relaxation
     easier.
- **Certificates.** Every LP bound reported is an exact rational dual evaluation (`certify`). A
  Lean check would need the 2968 labelled Q4 patterns, which `decide` can enumerate, and about
  330 rational multipliers. The bounds themselves, however, prove nothing new.

## Files

- `scripts/patterns.py`: forests and labelled patterns of Q_k up to symmetry (k ≤ 4).
- `scripts/forestlp.py`: the LP with hypergeometric face consistency. It builds the LP, solves it
  with HiGHS and evaluates the dual exactly with `certify`.
- `scripts/taglp.py`: the direction-tagged Sherali–Adams version.
- `scripts/run_lp.py`: runs both and writes `data/lp_k4.jsonl`, which holds the LP values and the
  exact bounds as fractions.
- `scripts/count5.c`: counts the induced linear forests of Q_k (14 911 for Q4, 64 233 113 for Q5).
- `scripts/fake_sa.c`: annealing for locally forest-like sets.
- `scripts/fakesat.py`: SAT for them. It uses milestone 29's `gforest.encode` and the Q4 8-cycle
  clauses.
- `scripts/fake_table.py`: the exact h tables in `data/fake_table.jsonl`.
- `data/fakesat_q7.jsonl`: the Q7 query that was abandoned.

Reproduce: `pip install --user highspy`; then, in `scripts/`, run `python3 run_lp.py hyper 5 6 7 8`,
`python3 run_lp.py tagged 5 6 7`, and `python3 fake_table.py 6 4`.
