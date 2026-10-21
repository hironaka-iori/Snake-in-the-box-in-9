# Global arguments beyond the local ceiling

Run of 21 October 2026. About 3.5 hours, with at most one core at nice 19, next to a Lean build. **Status: analysis and small computations only. No bound changes and nothing here is a Lean theorem.**

## Question

Every upper bound in the chain has the same shape. One global identity, the square census `T + 2 s0 = 9214 - 35 v`, is combined with local lower bounds on `α`. [Milestone 11](../11-local-ceiling/README.md) shows that local methods of the current type stop near 227, because of fibre-union adversaries. The share refinement could reach 222–229. This milestone asks whether a *different global inequality* moves that ceiling, and evaluates the candidate directions with small computations.

## Summary

| direction | what it gives at n = 9 | verdict |
|---|---|---|
| Coordinate directions / layers (halves are linear forests in Q8) | at least 224 even with exact Q8 packing data (the true value is unknown, somewhere in 224–255); calibration: 27–28 edges at n = 6 (truth 26), 55–63 at n = 7 (truth 50) | not competitive |
| Delsarte LP on the distance distribution (Krawtchouk positivity) | 237, identical to the current chain; it is weaker than `s0 ≥ 0` for v ≥ 220 | adds nothing |
| Huang with augmentation (`|S ∪ X| ≤ 256` when λ₁(A_s[S ∪ X]) < 3) | 255 with any local certificate; every set tested augments spectrally to exactly 256 | dead end in local form |
| Literature bounds (Snevily, Zémor, Solov'eva, Emelyanov–Lukito type) | all ≥ 250 at n = 9 | much weaker than 237 |
| **Subcube census for k = 3** (`Σ_x w_3(x) ≤ 5376`) | known adversaries give floors of 225 and 210, against 234 and 223 for the square census; real-snake slack is 0.4 % instead of 9 % | **most promising** |

The new idea is a family of exact global inequalities, one for each subcube dimension k. The repository identity is the case k = 2. For k = 3 the global slack, which comes from the empty subcubes, almost disappears. That slack is the reason the `s0` term limits the current method. The lever is then local again: windows must bound the mean of `w_3` from below. That needs a new window objective, not new mathematics.

## 0. What the square identity really says

Write `D2` for the number of pairs of snake vertices at distance 2. Every square holds at most 3 snake vertices, and 3 only for consecutive triples, so there are `v - 2` of those. Counting incidences gives

```
T  = 23 v + 10 - 2 D2,        s0 = 4602 - 29 v + D2 .
```

The local windows bound `T` from below, which means they bound `D2` from above. `s0 ≥ 0` is the only global input, and it bounds `D2` from below. Every global improvement therefore has to be a better lower bound on `D2`, or on some other count with a known total.

## 1. Coordinate directions and layers

For direction i, the two Q8 halves of a snake are induced linear forests. Together they have `n_i + 1` paths, and the two halves differ by at most one path. So `v ≤ g8(⌊(n_i+1)/2⌋) + g8(⌈(n_i+1)/2⌉)`, where `g8(c)` is the largest induced linear forest in Q8 with at most c paths. Since `min n_i ≤ (v-1)/9`, a bound of 236 would need `g8(13) + g8(14) ≤ 237`.

- Bank snakes are very unbalanced. Their direction counts look like `1,4,6,8,27,30,35,36,44`. When some `n_i = 1`, the layer bound with `a(8) = 98` gives at once `v ≤ 198`. So the argument does prove something: a snake beyond about 200 must use every direction many times. It cannot finish the proof, though, because nothing global penalises balanced direction usage.
- **Calibration with exact values** (`forest_pack.py`, SAT with lazy cycle cuts).
  - In Q5: `g5(1) = g5(2) = 14`, `g5(3) ∈ {14, 15}`, `g5(4) = 16`. The layer bound at n = 6 is therefore v ≤ 28 or 29, that is 27–28 edges, against the truth of 26 and Huang's 31.
  - In Q6: `g6(1) = 27` (from a(6) = 26), `g6(2) ≥ 28`, `g6(3) ≤ 30`, `g6(4) ≤ 31`. At n = 7 the bound lies between 55 and 63 edges, against the truth of 50 and Huang's 63. The lower end holds because `g6(4) ≥ 28` already allows v = 56.
- **Lower bounds for g8** (`fibre_forest.py`). These are fibre constructions `Q8 = Q_m × Q_{8-m}` with disjoint forests A and B alternating by parity.
  - `g8(4) ≥ 104` and `g8(8) ≥ 112`.
  - Q5 fibres give exactly 28 for (1,1), (1,2) and (2,2) paths (UNSAT above 28). Extra paths do not help in Q5.
  - `g8(12) ≥ 112` (Q6, 3+3 paths), and `g8(32) = 128` (Q4, 2+2 paths).
  - So `g8(13) + g8(14) ≥ 224`. Deciding whether it is below 237 is an exhaustive problem harder than a(8) = 98 itself. A direct SAT search for a 119-vertex forest with 13 paths in Q8 was UNKNOWN after 600 s and 152 cycle-cut rounds.
- **Within the census framework, layers add nothing.** Applying the Q8 identity to each half is the Q9 identity with the crossing squares removed. It is dominated by the Q9 identity.

Verdict: valid, but even with perfect Q8 data the bound cannot go below 224, and it could be as weak as Huang's. It is useful only as a structural lemma ("extremal snakes are direction-balanced").

## 2. Delsarte LP (`delsarte.py`, exact rational simplex `lp.py`)

The variables are the distance distribution `A_1..A_9`, with `A_1 = 2(v-1)/v`, `Σ A_i = v` and every Krawtchouk inequality. The table gives the range of `A_2` allowed at each v (`data/delsarte_n9.txt`):

| v | Delsarte only | `s0 ≥ 0` only | both |
|---|---|---|---|
| 200 | 13.46–30.5 | ≥ 11.98 | 13.46–30.5 |
| 238 | 19.08–32.9 | ≥ 19.33 | 19.33–32.9 |
| 256 | 22.05–34.0 | ≥ 22.05 | 22.05–34.0 |

For every relevant v, the lower bound on `A_2` from Delsarte is *weaker* than the one from `s0 ≥ 0`. Combined with `T ≥ (51/14) v`, it reproduces exactly 237. The integer-convexity bound of Snevily type on outside degrees (`Σ_y C(k_y,2) = 2 D2 - (v-2)` with `Σ k_y = 7v + 2`) gives `A_2 ≥ 18.87` at v = 238, which is also weaker. A Schrijver-type three-point SDP was not run, because no SDP solver is installed. It cannot see connectivity either: the 256-vertex union of 8-cycles from §3 satisfies every distance-distribution and three-point constraint that a snake does, except for the exact `-2` endpoint terms. So its only possible contribution is a slightly better lower bound on `A_2`. Each unit of `A_2` near v = 230 is worth about 5–6 vertices, so this is not worthless. But the Delsarte result suggests that the gain is small.

## 3. Huang with augmentation (`huang_aug.py`, `huang_highk.py`)

If `λ₁(A_s[U]) < 3` for the Huang signing, then `|U| ≤ 256`. If a snake S can always be augmented by a locally certified set X of outside vertices, then `v ≤ 256 - |X|`. The condition is local through Gershgorin on `A_s[U]²`: every vertex x of U needs `deg_U(x) + e_U(x) ≤ 8`, where `e_U(x)` counts the vertices of U at distance 2 from x with exactly one common neighbour in U. Two common neighbours cancel, because every square is negative.

Findings (`data/huang_aug.txt`, `data/huang_highk.txt`):

- **The spectral test augments every set tried to exactly 256**: three bank snakes (v = 192, 64 added), adversary208 and adversary224. It works even using only outside vertices with at least 5 snake neighbours (64 of 160 candidates). Huang is tight for all of them.
- **Gershgorin, the local version, admits no outside vertex with 5 or more snake neighbours.** It reaches 225–226 on bank snakes and 256 on the adversaries, but only through vertices with at most 4 snake neighbours.
- At v = 238 the identity together with `T ≥ 3.64 v` forces the outside degrees to have mean 6.09 and variance at most 1. A distribution with every outside degree in {6, 7} satisfies all counts, so a dense hypothetical snake may offer no admissible vertex at all.

Verdict: the local form gives nothing below 256. The exact form gives nothing either, since every set saturates Huang. This direction is closed.

## 4. Literature

The published general upper bounds are all of the form `2^{n-1}(1 - o(1))`:
- Snevily: `2^{n-1}(1 - 1/(20n-41))`, stated for large n, which gives about 254 if evaluated at n = 9;
- Zémor: a correction of order `n^{-1/2}`;
- Solov'eva and Emelyanov–Lukito: refinements for coils and small n.

None is below about 250 at n = 9. I could not recheck the exact constants offline. What these arguments share is a neighbourhood-counting core: outside vertices have bounded numbers of snake neighbours. In the notation of §0 that core is the convexity bound on `D2`, and §2 shows it is weaker than `s0 ≥ 0`. The repository's local data already exceed all of them by a wide margin.

## 5. The subcube census family (`subcube_census.py`)

For a vertex set S, a subcube dimension k and `x ∈ S`, define

```
w_k(x) = Σ_{k-subcubes Q ∋ x} 1 / |Q ∩ S| ,      N_k = C(9,k) 2^{9-k},
Σ_{x∈S} w_k(x) = N_k - E_k ≤ N_k ,    E_k = # k-subcubes disjoint from S.
```

This is double counting: each nonempty subcube distributes weight 1 equally among its snake vertices. For k = 2 it is exactly the repository identity, since `2 w_2(x) - α(x) = 36 - n3(x)/3` holds pointwise. A local method that proves `mean w_k ≥ μ_k` gives `v ≤ N_k / μ_k`. For 236 edges (excluding v = 238) the requirement is `μ_3 > 5376/238 = 22.59`. 230 edges needs `μ_3 > 23.17`, and 222 edges needs `μ_3 > 24.0`.

Census of known sets (`data/subcube_census.txt`). The floor is `N_k / mean(w_k)`, the best bound that any local `w_k` method can prove if it cannot tell the set from a snake:

| set | k = 2: empty, floor | k = 3: empty, floor | k = 4: empty, floor |
|---|---|---|---|
| bank snakes (v = 192) | 8.8 %, 210.6 | 0.3–0.6 %, 192.6–193.1 | 0, 192.0 |
| adversary224 | 4.2 %, 233.7 | 0.6 %, **225.3** | 0.1 %, 224.2 |
| adversary208 | 6.6 %, 222.7 | 0.9 %, **209.9** | 0.1 %, 208.3 |

Why this matters:
- The `s0` problem of milestone 11 is that empty squares carry `2 s0 / v ≈ 4.2` per vertex of real-snake slack, which local `α` cannot see. Almost every empty square lies inside a *nonempty* 3-cube, so the 3-cube census charges it canonically and exactly, with no share design.
- The adversary floors fall from 234 to 225 (radius-3, four-centre type) and from 223 to 210 (radius-4 or five-centre type). These are the same numbers that the `s0`-exact share method would reach (milestone 11: about 207), but here they come from plain windows.

**Local data.**
- *Pointwise minimum* (`wkmin.py`, weighted MaxSAT on the radius-3 ball around an internal vertex, with path-degree and endpoint constraints and lazy cycle cuts): `min w_3 = 21`, which is exactly `5376/256`, Huang's level. Radius 2 gives `min w_2 = 35/2`, and radius 4 gives 18, which corresponds to α = 1 and reproduces the singleton lemma. So pointwise bounds give nothing, exactly as for `α`. Averaging over windows is needed.
- *Bank data* (`data/bank_w3.txt`, all 131 snakes):
  - the minimum `w_3` at an internal vertex is 22.78;
  - the mean is 27.8–27.9;
  - empty 3-cubes number 15–36 out of 5376;
  - the minimum of `w_3` by `α` is 22.78 at α = 3, 23.45 at α = 4, 24.53 at α = 6, 26.5 at α = 9 and 29.5 at α = 12, a slope of about 0.65 per unit of α.
- *Transfer from the current automaton does not help.* A pointwise lemma of the form `w_3 ≥ 21 + 0.6(α - 1)` with mean `α ≥ 51/14` gives `μ_3 ≈ 22.59`, that is 237 again. The gain must come from windows that score `w_3` directly. `w_3` sees the distance-3 structure that `α` and `s0 ≥ 0` miss.
- The radius-4 MaxSAT runs (pointwise, and conditioned on α ≥ 2) did not finish in 25 and 10 minutes with RC2. No window-level value of `μ_3` has been computed.

## What it would take

1. **Lean, global part (easy).** Prove `Σ_{x∈S} w_3(x) + E_3 = 5376` for every `S : Finset (Fin 9 → Bool)`. Use the same double-counting style as `SquareIncidence.lean`, with 3-cubes indexed by a 3-subset of coordinates and a base point. Use integers by scaling by 60, since `60/|Q ∩ S| ∈ {60,30,20,15,12}` for path patterns: a 3-cube meets a snake in at most 5 vertices. Then `60 Σ w_3 ≤ 322560`.
2. **Window side (the real work).** Replace the `α`-count objective of the radius-4 window encodings (`wincert.Encoding`, the five-centre direction automaton) by `60·w_3` at the centres. The ball must cover the radius 3 around each centre, which radius-4 windows do. This is a weighted threshold, like the T5 share thresholds of the `s0` loop, so the existing PB/cardinality machinery, DRAT/LRAT certification and Lean bridge carry over. The only new soundness lemma is that the clause encoding computes `|Q ∩ S|` for the 84 cubes at a centre.
3. **Targets.** Exclude v = 238 (236 edges) with window mean `μ_3 > 22.59`. The plausible range, by analogy with how close the α automata came to their floors (227 against 222.7), is around 212–218. That is not proved: the next experiment is a k = 3 or k = 5 window survey of the minimum mean `w_3`, using a faster MaxSAT or a threshold-SAT search instead of RC2.
4. Combining the k = 2 and k = 3 censuses with weights (`λ Σ w_2 + Σ w_3 ≤ λ N_2 + N_3`) is free, and may help the window side where `α` is the stronger signal. The k = 4 census has zero real-snake slack but needs radius-4 data around every centre.

## Files

- `scripts/lp.py`: exact two-phase simplex (Fractions).
- `scripts/delsarte.py`: the Delsarte LP and the `s0` and `μ` constraints.
- `scripts/huang_aug.py`, `scripts/huang_highk.py`: Huang augmentation (spectral and Gershgorin).
- `scripts/subcube_census.py`: `w_k`, `E_k` and the floors for bank snakes and adversaries.
- `scripts/wkmin.py`, `scripts/wkmin2.py`: weighted MaxSAT for the pointwise minimum of `w_k`.
- `scripts/bank_w3.py`: `w_3` statistics and the α relation over the bank.
- `scripts/forest_pack.py`, `scripts/fibre_forest.py`: `g_m(c)` and the fibre constructions for the layer argument.
- `data/*.txt`: the outputs quoted above.

The scripts need numpy and python-sat. `forest_pack.py`, `fibre_forest.py`, `wkmin*.py` use CaDiCaL through python-sat.
