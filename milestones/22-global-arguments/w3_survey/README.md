# The w_3 window survey

Run of 21 October 2026. It took about 4 hours on one core at nice 19, next to a Lean replay build. **Everything here is solver-side. Nothing is a Lean theorem, and no bound in the chain changes.**

The question was whether the 3-cube census of `../README.md` §5 beats the α route on radius-4 windows, and by how much.

## Answer

| | rigorous now | if all 11,425 window keys reach T5 ≥ 1380 / 1400 / 1420 | ceiling (SAT witnesses) |
|---|---|---|---|
| **w_3 charge, five-centre radius-4 windows on the L7 k5 K5 automaton** | **m ≤ 240** (964 keys tested) | 235.8 / 232.5 / 230.1 | **≈ 230** (229.95) |
| direction-only five-centre windows (no α in the key) | m ≤ 247 | — | — |
| α route, same automaton (milestone 10) | 237 (387 windows), 236 (732 windows) | — | about 227 (milestone 11) |
| s0 share route (milestone 11, `s0_share_loop`) | 234 (484 share + 835 plain windows) | — | 230.9 |

- The w_3 route **does not beat the α route at an equal number of certificates**. With about 900 window certificates it proves 240. The α route proves 236 with 732.
- It overtakes the α route only near full coverage of the 11,425 five-centre keys. All keys at T5 ≥ 1380 would give 235. Keys at 1420 would give 230, which is the ceiling.
- Its ceiling of about 230 equals the share route's 230.9. The certificates are simpler (no share machinery) and mostly much smaller than α-route refutations, but there are far more of them.

## The charge and the global inequality

The census is used in integer form, with `h(n) = ⌊12/n⌋`, that is 12, 6, 4, 3, 2 for n = 1..5. A 3-cube meets a snake in at most 5 vertices.

```
c(x) = Σ_{3-cubes Q ∋ x} h(|Q ∩ S|),     Σ_{x∈S} c(x) = Σ_{Q ≠ ∅} |Q∩S|·h(|Q∩S|) ≤ 12·5376 = 64512.
```

- `c ≤ 12 w_3`, with equality unless a cube through x holds 5 snake vertices.
- On the bank snakes the loss is 0.36 c-units per vertex (0.03 in w_3 units). The census totals are 64000–64266 against 64512, a slack of 0.4–0.8 % (`data/controls.json`).
- Bank snakes have mean internal c = 333.98 (27.83 w_3), minimum 273, and a minimum five-window sum of 1462.

**Final arithmetic.** Take a snake with m edges and internal vertices x_1..x_{m-1}, and let `W_j` be the window of centres j..j+4. Let λ = P/Q be the minimum cycle mean of the window lower bounds T5, and R the range of an integer potential for `Q·T5 − P`.

- Every internal vertex lies in at most 5 windows. The 20 missing incidences at the two ends each carry `c ≥ 257`, the single-centre minimum.
- `W_1` and `W_2` are dropped, because the automaton state needs seven directions.
- Endpoints have `c ≥ 84·2 = 168`.

Then

```
5 Σ_{j=1}^{m-1} c(x_j) ≥ (P(m−7) − R)/Q + 5140   and   Σ_{j=1}^{m-1} c(x_j) ≤ 64512 − 336,
so   m ≤ 7 + (315740 Q + R) / P        (≈ 7 + 63148/μ, with μ = λ/5 the per-vertex mean of c).
```

This is the analogue of `m ≤ 9171/(μ+35)`. The thresholds are:

| m ≤ 236 | 235 | 233 | 230 |
|---|---|---|---|
| μ > 274.6 (22.88 w_3) | 275.8 | 278.3 | 281.9 (23.49 w_3) |

These sit slightly above the README's 22.59, because of the boundary terms and the `h(5)` rounding.

## Encoding (`w3enc.py`)

`W3Encoding(window, alpha, radius=4, cap)` is `wincert.Encoding`, unchanged, followed by these clauses for each centre and each of its 84 cubes:

- a downward totalizer over the cube's 7 other corners;
- indicators `y_j ∨ g[j+1]` (j = 3, 2, 1, 0; `y_j` is forced when at most j other corners are selected; levels made impossible by the path neighbours are skipped);
- one upward totalizer over the `y`'s, repeated by weight 1, 1, 2, 6, which is `h(1+r) − 2`. It is truncated at `cap − 168k + 1`, with a final unit.

In every configuration of the local model, the forced `y`'s give exactly `Σ c − 168k`. So UNSAT means `Σ_centres c ≥ cap + 1`.

The radius-4 ball contains every 3-cube through every centre, and every vertex at distance ≤ 3 has its full neighbourhood in the ball. Positive controls passed 60 out of 60: on bank windows, the CNF is SAT under the snake's own selection with `cap` equal to the true charge, and UNSAT with `cap` one lower.

**Symmetry breaking** (`sym_break`, on by default) adds lex-leader clauses `x ≤_lex σx` for every transposition of two coordinates the window does not use. The model, α and c are all invariant under these transpositions, so this is sound for lower bounds. It speeds up the single-centre UNSAT proofs by 30–50×: T = 257 takes 1.4 s instead of 48 s, and α = 2 at T = 262 takes 11 s instead of more than 600 s. A Lean replay would need a lex-leader lemma, or proofs without symmetry breaking (see the costs below).

## Results

**Single centre** (`w3survey.py`, `data/w3_oracle.jsonl`). The radius-4 minimum is exactly **257** (21.42 w_3), against 21 at radius 3. That gives m ≤ 252 by itself.

Conditioned on α, the proved minima (with the best witnesses) are:

| α | 1 | 2 | 3 | 4 | 5 | 6+ |
|---|---|---|---|---|---|---|
| lb (ub) | 257 (257) | 263 (263) | 267 (279) | 271 (275) | 274 (302) | 279 (306) |

The slope is about 4 c per unit of α, against 8 c on the bank. With the α automaton's mean, single-centre bounds alone give about 239–240.

**Direction-only five-centre windows** (9 shapes; `data/shape_aut_k5.json`). The proved lower bounds are 1315–1322 within 4 minutes per shape. The minimum mean is 2631/2, that is 21.93 w_3, which gives **m ≤ 247**. The direction-only witnesses found here are poor (≥ 1574), but every α-conditioned witness below is also a direction-only witness. Without α, the window minimum is close to 5 × the pointwise minimum.

**Alpha-conditioned five-centre windows** (`refine_w3.py`, `sweep_w3.py`, `ceiling_probe.py`, `data/w3_alpha_oracle.jsonl`).

The automaton is the radius-4 L7 k5 K5 automaton of the 237/236 chain: 44,064 states and 240,729 edges, already pruned by the radius-4 α exclusions, with 11,425 five-centre keys. The edge weight T5 is the proved threshold lower bound of the key, or a dynamic-programming bound over proved sub-windows (single-centre α minima, direction-only shapes, α-conditioned pairs and triples).

- Refinement (24 rounds) and two sweeps of the incremental per-shape solvers tested 964 keys. At T = 1420, about 90 % were UNSAT, most in under 15 s (median 0.5 s incremental); 9 % timed out and under 1 % were SAT.
- **Rigorous: λ = 22995/17 = 1352.6 (22.54 w_3), with exact potential range 406, so m ≤ 240.44, that is m ≤ 240** (`data/w3_eval.json`).
- **Trend.** The rigorous minimum cycle always runs through untested keys whose weight is the DP floor (about 1345–1360). This is the same pattern as the share loop. The bound rose by about 0.003 w_3 per round, roughly 0.5 edge per CPU-hour of refinement.
- The sub-windows add almost nothing. α-conditioned pairs and triples reach their single-centre floors: (3,3) gives 534 = 2·267, and many triples are α-infeasible. So the gain lives only in five-centre windows.
- **What-if** (not rigorous): untested keys at `min(F, ub)`:

  | F | 1380 | 1400 | 1420 |
  |---|---|---|---|
  | m ≤ | 235.8 | 232.5 | 230.1 |

- **Ceiling (rigorous).** A period-6 cycle of SAT witnesses has mean λ = 8497/6 = 1416.2 (23.60 w_3), so **m ≤ 229.95 is the best this window family can give on this automaton**.
  - The cycle uses shapes (0,1,2,3,0,4) / (0,1,2,3,0,1) with α (3,5,3,4,5), (4,5,4,3,5) and (3,4,5,4,3).
  - Its window values are 1423, 1418, 1412 (proved exact), 1418, 1423 and 1403.
  - The lowest witness found anywhere is 1393, for (0,1,2,3,0,1) with α (3,4,3,3,5).
  - So 230 needs essentially all 11,425 keys certified at about 1416–1420. Below 229 needs k ≥ 6, L = 8 or radius 5.
- **The adversaries do not limit this family** (`data/adversary_ceiling.json`). Every radius-4 five-centre ball of adversary224 (14-cycles) and adversary208 (26-cycles) contains a whole cycle of the adversary, which the cycle cuts exclude. adversary208 passes 96 of its 208 three-centre windows. Their census floors (226.0 and 210.7) therefore do not apply at radius 4 with five centres; the witness ceiling of about 230 is the binding one.

## Certificates and Lean cost

The basis is the 237 rate: 34 kernel-hours for 289 M hints, about 0.42 ms per hint. Proofs were measured with CaDiCaL 2.1.3 `--lrat`, trimmed to the empty clause and deleted after measuring.

- **Five-centre thresholds, with symmetry breaking.** There were 40 samples inside the loop, at T = 1360–1420.
  - The median is **24 k hints**, the mean 0.44 M, the 90th percentile 1.9 M and the maximum 3.4 M. One sample exceeded the 120 MB file cap.
  - The CNFs have about 40 k variables and 1.35–1.48 M clauses (29–32 MB).
- **Without symmetry breaking.** Easy windows are unchanged: 264 against 264 hints, and 10.8 k against 7.8 k. A hard window (3.4 M hints with symmetry breaking) exceeded the 120 MB cap without it (`data/proof_sample.jsonl`).
- **Single-centre α minima are the expensive ones.**
  - T = 257 needs 1.56 M hints with symmetry breaking, and more than 120 MB of proof without it.
  - α = 2 at T = 263 is over the cap even with symmetry breaking.
  - α = 3..6+ at their minima do not refute cold within 120 s.
  - These are seven certificates, each plausibly 10–100 M hints. Using them below their minima (for example 266 instead of 267) is far cheaper.
- **Totals.**
  - The current rigorous set (240) uses 888 threshold certificates and the single-centre certificates, plus the α exclusions already built into the automaton.
  - At the sampled mean, 888 certificates cost about 50 kernel-hours. A converged set of about 11,000 certificates is about 5 G hints, roughly **600 kernel-hours**, or about 30 at the median if the tail can be cut. On top of that come a few heavy single-centre proofs and a new Lean lex-leader lemma.
  - The 236 chain cost 34 kernel-hours. The share route's estimate was 1,000–2,500 kernel-hours.

## Recommendation

Do not switch the 236 chain to w_3 windows. At equal certificate counts the w_3 route is worse (240 against 236), and its ceiling of about 230 is no better than the share route's 230.9. Its real advantages are:

- a clean global identity;
- small certificates for most keys;
- a near-zero real-snake slack.

If 230–233 is the next goal, first run a complete solver-side sweep at T = 1400 over all 11,425 keys, using `sweep_w3.py` with per-shape incremental solvers. That is about 3–4 CPU-hours, and it would establish about 232.5 solver-side. Then decide on Lean.

The binding windows are period-3 patterns with α = 3–5 on shapes (0,1,2,3,0,x). Getting below 230 needs six-centre or radius-5 windows on those. A census with weights, `λ·(k = 2) + (k = 3)`, could also be tried there, since the α route already excludes many of the low-α patterns.

## Files

- `w3enc.py`: the charge, the encoding, symmetry breaking, the lazy-cut solve, `measure_proof`.
- `controls.py`: bank calibration and positive controls (`data/controls.json`).
- `w3survey.py`: exact incremental minimum per key (direction-only shapes, single-centre α); `data/w3_oracle.jsonl`.
- `shape_aut.py`: the direction-only automaton (`data/shape_aut_k5.json`).
- `refine_w3.py`: the refinement loop on the α automaton (`data/w3_rounds.jsonl`), with the DP over sub-windows.
- `sweep_w3.py`, `sub_sweep.py`: incremental per-shape threshold sweeps (five-centre keys; 2- and 3-centre α keys).
- `ceiling_probe.py`: the witnessed-cycle ceiling (`data/ceiling_probe.jsonl`).
- `eval_w3.py`: the rigorous mean with exact potential, the ceiling and the what-ifs (`data/w3_eval.json`).
- `adv_check.py`: the adversary windows; `proof_sample.py`: LRAT sizes; `summarize.py`: `data/summary.json`.
- All solver results are in `data/w3_alpha_oracle.jsonl`, one line per call. The automaton is read from the compact form of the share loop (`STAGE3` scratch: `aut_compact.npz`, `aut_keys.pkl`, rebuilt by `../../11-local-ceiling/s0_share_loop/refine_share.py:load_compact`).
