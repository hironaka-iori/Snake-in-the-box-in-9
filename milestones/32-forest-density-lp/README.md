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

RESULTS_PLACEHOLDER
