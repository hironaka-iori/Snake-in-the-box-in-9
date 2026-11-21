# Milestone 43: Fourier, spectral and polynomial-method bounds

Run of 21 November 2026, one 4-core machine. **No new bound is claimed.** Bounds are in **edges**
unless marked "vertices" (V = edges + 1). Truth: a(7) = 50, a(8) = 98, and 191 <= a(9) <= 231 (Lean).
Nothing here is a Lean result. Section 3.1 has two short complete proofs; every other number is either
exact-rational arithmetic (marked) or floating-point exploration (marked "numerical").

## Answer

None of the Fourier, spectral or polynomial methods tried here gets below 254 for Q9. Most of them do
not even reach Huang's 255. Two reasons:

1. **Barrier from independent sets (proved, section 3.1).** Suppose a method bounds `lambda_max(M[S])`
   by local data (edge weights and diagonal), and the same estimate holds for an independent set. Then
   the method cannot beat 2^{n-1} vertices, for any matrix M supported on the cube. The even half-cube
   is such an independent set. To go lower, a method has to use that the path is connected.
2. **Augmented Huang is exact, so it gains nothing by itself (section 3.2).** Huang's interlacing still
   applies after adding vertices. `|S| + |I| <= 2^{n-1}` whenever `lambda_max(A_s[S u I]) < sqrt(n)`.
   Numerically, greedy search extends **every snake tested to exactly 2^{n-1} vertices**. So "every
   snake has an augmentation of size >= 26" is not a weaker lemma: it is a restatement of a(9) <= 229.
   Its content has to come from a *local* certificate for the augmentation. The natural local
   (Collatz) certificate recovers only about half of the slack, even on the record snakes.

Ranking. All of these are at or above 254 at n = 9, so none is useful for the 229 target.

| # | method | n = 7 | n = 8 | n = 9 | status |
|---|---|---|---|---|---|
| 1 | Huang signed interlacing (`SpectralUpperBound.lean`) | 63 | 127 | 255 | proved (project) |
| 2 | second moment of outside counts c(w) + square identity `T >= V` | 62 | 126 | 254 | exact arithmetic; equals the existing 254 |
| 3 | Delsarte = level-weight Fourier LP with `s0 >= 0`, `T >= V` (milestone 41) | 62 | 126 | 254 | exact LP |
| 4 | augmented Huang with local Collatz packing | – | – | – | no unconditional bound; it would need a lower bound on the packing for hypothetical snakes |
| 5 | path-spectrum interlacing over all signings of Q_n | (63) | – | – | numerical: no signing beats Huang (n = 6, 7) |
| 6 | Fourier levels with parity correction (Hoffman type) | 73 | 145 | 286 | exact, weaker than Huang |
| 7 | Hoffman ratio / total influence (unsigned A) | 81 | 158 | 311 | exact, weaker than Huang |
| 8 | level-k inequalities, hypercontractivity, KKL / Friedgut | – | – | trivial | densities near 0.45, so the constants make them vacuous |
| 9 | sensitivity / GF(2)-degree / Nullstellensatz | – | – | none | see section 4 |

The general formulas are:

- Row 1 is `2^{n-1} - 1`.
- Row 2 is `2^{n-1} - 2` for n = 5..11 (`scripts/cs_moment.py`).
- Row 7 is the largest V with `2(V-1) >= 2nV^2/2^n - nV`, i.e. about `2^{n-1}(n+2)/n`.
- Row 6 is about `2^{n-1} n/(n-1)` (`scripts/fourier_levels.py`).

## 1. Fourier levels (exact, `scripts/fourier_levels.py`, `scripts/cs_moment.py`)

Let f = 1_S. Its Fourier weights satisfy `sum_T fhat(T)^2 (n - 2|T|) = 2(V-1)/2^n`, so the edge count
pins a linear combination of the level weights W_k. This is exactly the information the Delsarte LP
uses: the distance distribution and the level weights are Krawtchouk transforms of each other. The
Delsarte LP therefore already subsumes every inequality that is linear in (W_0, ..., W_n). Milestone 41
found 254 for it.

The extras tried:

- **Hoffman.** The only negative eigenvalue that matters is -n (the parity character), which gives
  311 edges for n = 9.
- **Hoffman with parity correction.** An induced path has |V_e - V_o| <= 1, so W_n <= 4^{-n}. This
  gives 286.
- **Convexity / second moment.** Count each distance-2 pair through its two common neighbours:
  `2 D2 = sum_{w notin S} C(c(w),2) + (V-2)`. The minimum, by bipartite side and with integer c, is
  combined with `D2 <= 11V + 5`, which is the singleton-square bound `T >= V`. Only V = 256 is excluded,
  which reproduces the existing 254.
- **Level-1 / Chang / Talagrand, KKL, Friedgut, hypercontractive level-k bounds.** These bound
  low-degree weight for sparse sets. At μ = 231/512 ≈ 0.45 each is weaker than the trivial
  `W_1 <= μ(1-μ)`, e.g. `2μ^2 ln(1/μ) ≈ 0.32 > 0.248`. Every influence `I_i` is about `(n-2)μ/n`, so
  no influence is small. These tools are asymptotic, and their constants make them vacuous at n = 9.

## 2. Polynomial view: Huang as a dimension count (proved; it is a reformulation, not a new bound)

Let A_s be Huang's signed matrix, with A_s^2 = nI, and let W be its +√n eigenspace (dim 2^{n-1}). Let
`W_0 = {x in W : x|_S = 0}`.

The restriction map W -> R^S is onto. If it were not, some nonzero y supported on S would be
orthogonal to W. Then y would lie in the -√n eigenspace, which forces `lambda_min(A_s[S]) = -√n`,
impossible for a path (its eigenvalues are > -2). Hence, for every snake, exactly
**dim W_0 = 2^{n-1} - V**.

So `a(9) <= 229` holds if and only if every snake has at least 26 linearly independent
3-eigenvectors of A_s that vanish on S. These are the "polynomials" of the method. Natural ones are
`x = (A_s + 3I) e_v` for v at distance >= 2 from S: they are supported on the closed ball of v. There
is no reason a hypothetical dense snake has any such v. The CS decomposition of the involution A_s/√n
also shows that the signed spectrum of the complement Q_n - S is determined by that of S:
`-spec(A_s[S])` together with ±√n, each `2^{n-1} - V` times. Interlacing on the complement or on a
neighbourhood therefore gives nothing beyond Huang.

## 3. Spectral

### 3.1 Two short proofs

**(a) Augmented Huang.** Let I be disjoint from S with `lambda_max(A_s[S u I]) < sqrt(n)`. Then
`|S| + |I| <= 2^{n-1}`.

Proof: if not, `R^{S u I}` meets W nontrivially, and that vector has Rayleigh quotient √n. ∎

For example, any I of vertices with c(w) <= 3 works at n = 9 if a Collatz vector certifies the bound:
cost c(w)/3 at each S-neighbour, capacity 1 at interior path vertices and 2 at the endpoints, I
independent. The strict inequality comes from the endpoint slack and Perron–Frobenius on |A|.

**(b) Independent-set barrier.** Let M be any symmetric matrix on V(Q_n) supported on the edges and
the diagonal, and let t be a threshold. Suppose the bound `V <= #{eig(M) < t}` is justified by
`lambda_max(M[S]) < t`, for every snake S, through an estimate in edge weights and diagonal entries
alone. That estimate then also holds for the even half-cube H (an independent set, so M[H] is
diagonal). Interlacing on H gives `#{eig(M) >= t} <= 2^{n-1}`. So the method cannot beat 2^{n-1}
vertices. ∎

### 3.2 Augmentation numerics (numerical, `scripts/huang_aug.py`, `scripts/aug_random.py`)

Greedy search adds vertices while keeping `lambda_max < √n`, checked with numpy `eigvalsh` (tolerance
1e-9).

| snake | V | Huang slack `2^{n-1} - V` | greedy augmentation | local Collatz packing |
|---|---|---|---|---|
| Q8 witness (`outputs/snake8_witness.json`) | 99 | 29 | **29** | 15 |
| Q9 191-edge witness | 192 | 64 | **64** | 34 |
| 5 random snakes Q6 (V = 23-24) | | 8-9 | = slack | – |
| 5 random snakes Q7 (V = 37-43) | | 21-27 | = slack | 16-21 (n = 9 costs; not a valid certificate for n = 7) |
| 3 random snakes Q8 (V = 64-66) | | 62-64 | = slack | 37-46 (same caveat) |

The augmentation reached `2^{n-1}` in every case tried. **Conjecture (numerical): every induced path
of Q_n extends to an induced subgraph on 2^{n-1} vertices with signed `lambda_max < √n`.** If this is
true, augmented Huang with an exact augmentation is vacuous: it never excludes any length. Only a
local *certificate* for the augmentation could turn it into a method. That certificate is again a
local statement about S, of the kind the window machinery proves. Milestone 41's locality ceilings
(223 for Q4-local information, 207 for Q5) apply to the local part.

The local Collatz packing captures 50-55 % of the slack on the record snakes. It captures less on
denser ones, and nothing forces it to be positive for a hypothetical 231-vertex snake. For example,
`4(512 - V) <= 7V + 2` allows every outside vertex to have c >= 4 once V >= 186.

### 3.3 Path-spectrum interlacing over signings (numerical, `scripts/signing_search.py`, `scripts/forest_barrier.py`)

This uses the whole spectrum of the path, not just λ_max. If M is any ±1 signing of Q_n, an induced
P_V forces `lambda_k(±M) >= 2cos(kπ/(V+1))` for all k <= V. This family *does* see connectivity:
independent sets do not have the path's spread spectrum. It is also not confined to subcubes.

- **Huang's signing** gives exactly V <= 2^{n-1}. The unsigned cube gives V <= 382 at n = 9.
- **Hill climbing over single edge flips** (n = 6: 20,000 steps from the Huang, random and all-plus
  signings; n = 7: 4,000 steps from Huang) found **no signing better than Huang**. Huang was a strict
  local optimum of the violation margin.
- **A lower limit, from forests.** For every induced forest F and every signing M,
  `lambda_k(M) >= lambda_k(F)`. A forest that spectrally dominates P_V therefore stops every signing
  from excluding V. Annealing found dominating forests for V = 26 (n = 6) and V = 46 (n = 7)
  (`data/forest_n*_V*.json`, validated as induced forests). These are below the truth (27 and 51
  vertices). So the barrier does not rule the family out, but the search found no signing that
  exploits the room.

## 4. Polynomial method

- **Sensitivity.** f = 1_S has sensitivity >= n - 2 at every interior path vertex, so Huang's
  `s(f) >= sqrt(deg f)` holds trivially. The graph form of Huang's theorem (row 1) is the only useful
  form.
- **GF(2) degree.** `deg_{F2} 1_S = n` exactly when V is odd. Otherwise it is unconstrained.
- **Combinatorial Nullstellensatz / Alon–Füredi.** These need a covering or vanishing structure that S
  or N(S) does not provide. The linear-algebra method that does apply is the dimension count of
  section 2, and it is exact, so it gives no slack.

## Files

- `scripts/huang_aug.py`: Huang matrix and greedy augmentation on a witness.
- `scripts/aug_random.py`: random snakes, greedy augmentation and local packing.
- `scripts/cs_moment.py`: second moment plus square identity (exact integers).
- `scripts/fourier_levels.py`: Hoffman and parity-corrected level bounds (exact rationals).
- `scripts/interlace_barrier.py`: star packings (weak greedy; superseded by `forest_barrier.py`).
- `scripts/signing_search.py`: hill climbing over signings.
- `scripts/forest_barrier.py`: dominating induced forests.
- `data/forest_n6_V26.json`, `data/forest_n7_V40.json`, `data/forest_n7_V46.json`.

## Suggested next step (if any)

The only route here with a non-local ingredient is augmented Huang combined with a **locally
certified augmentation**, i.e. a lower bound on the local Collatz packing in terms of window data.
That would be a new linear inequality, `V + P_loc <= 256`, which could be added to the existing window
LP. Whether it helps is untested. It would help only if a P_loc lower bound costs less than the window
certificates it replaces. The packing values above, about half the slack on real snakes, make a large
gain unlikely.
