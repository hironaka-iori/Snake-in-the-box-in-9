# Refinement loops on the six-centre (k = 6) direction automaton

Run of 21 October 2026: about 3.6 h on one core at nice 19, next to a Lean build. Everything here is solver-side. Nothing is a Lean theorem, and no proof was checked by drat-trim or Lean in this run.

**Units.**
- μ is the minimum cycle mean in α units, and the bare bound is m ≤ 9171/(μ+35).
- The Lean arithmetic of the plain chain is `(P + 35Q) m ≤ 9171 Q + C`, with `C = (2^B − 1) + 7P − 6Q` (`gen_lean_chain5.py`).
- C costs about 0.6 edges, so in that chain 235 needs μ > 3.95, 234 needs μ > 4.12 and 233 needs μ > 4.30.
- For k = 6 the leading-step constant may differ slightly. It has not been derived.

## Answer

| | (A) plain: 5- and 6-window UNSAT exclusions | (B) share: 6-window plain + 5-window share charges |
|---|---|---|
| rigorous μ | **65/16 = 4.0625, converged** (every window on the minimum cycle is SAT) | **1520/3 / 120 = 4.2222**, not converged, still rising |
| bare bound | m ≤ 234.78 | m ≤ 233.82 |
| Lean-chain bound | **235** (λ = 4: 39 m ≤ 9200, potential range 4) | **234** (estimated, using the same constant; the share chain's C has not been derived) |
| rounds / CPU | 72 rounds, 18 min | 98 rounds, 3.0 h (budget) |
| new certificates for the bound | **1,581**: 1,440 five-centre and 141 six-centre | for 234 (λ = 496, μ = 4.133): **2,426 plain** (1,458 five-centre, 968 six-centre) **+ 564 share** |
| base exclusions (radius-4 cache, inside the k5 pickle) | ≤ 1,685; the 236 set used 732 | ≤ 1,728 |
| automaton | 61,999 lifted nodes, 1.0 M edges; **51,201 live states**; full product 34 × 6^5 = 264,384 | the same graph; 49,835 live states |
| estimated hints | 0.9–3.7 G | 3–8 G |
| kernel-h at 0.42 ms per hint (237: 289 M hints, 34 h) | **≈ 110–430** | **≈ 350–950**, plus the share machinery (stages 4–5) |

## (A) Plain loop (`k6loop.py A`, `rounds_A.jsonl`)

**Automaton.** The automaton is the radius-4 L7 k5 K5 automaton of the share loop (the 240,729-edge pickle) lifted by one more remembered count, as in `../s0_k6_ceiling`:
- a k5 edge v → w becomes (v, a0) → (w, v.α[0]);
- the edge's 6-window key is that of the target's 7 directions with the counts (a0, v.α, new);
- the 5-window of every edge into a node (v, a0) is the same, so a 5-window exclusion removes nodes.

**Exclusions.** Exclusions are merged from:
- the radius-4 oracle cache;
- the plain calls of the share loop;
- `oracle5_extra`/`oracle6` of `../s0_k6_ceiling`;
- the new calls in `oracle_plain.jsonl`.

A key also counts as excluded when it contains a sub-window known to be UNSAT.

**Loop.** Each round tests every untested window on the minimum cycle: the 5-window first, then the 6-window.

**Progress.** The mean rose 23/6 → 43/11 → 4 (plateau, rounds 15–35) → 4.04 → **65/16** at round 71. The final 16-cycle has α = (3,6,3,6,3,3,6,3,2,6,4,6,2,3,6,3), and all of its 5- and 6-windows are SAT. So 4.0625 is the exact ceiling of plain exclusions at k = 6, radius 4. Going above it needs radius 5, k = 7 or shares.

**Calls.** 1,489 calls in total:
- 6-windows: 632 UNSAT, 210 SAT;
- 5-windows: 452 UNSAT, 193 SAT, 2 timeouts.

The median solve time was 0.07 s.

**Minimising (`minimal.py A --target 235`).** This uses the dual pruning of `minimize.py`, with λ lowered to the cheapest value that still gives 235. That value is λ = 4/1, with potential range 4 (3 bits). It keeps 1,581 of the 2,615 UNSAT keys that act on the lifted graph:

| source | kept keys |
|---|---|
| share-loop plain calls | 991 |
| new in this run | 553 |
| `../s0_k6_ceiling` | 37 |

At the converged λ = 65/16, 1,889 keys are kept, and the Lean bound is still 235.

**Base count (`base.py`).** `base.py` enumerates every candidate k5 edge that the pickle lacks. It keeps a blocker unless every k6 lift of the edge has non-negative slack. A lift whose end lies outside the graph gets the least admissible potential, or is kept when that cannot be decided. This conservative bound is ≤ 1,685 base keys, against 732 in the current 236 set. The truth lies in between.

## (B) Share loop (`k6loop.py B`, `rounds_B.jsonl`)

**Weights and tests.**
- The weight is 120·sym + T5_lb(key5), which is rigorous: untested windows count 0.
- The exclusions are the same as in (A).
- Each round, on the rigorous minimum cycle:
  - 6-windows get a plain solve;
  - 5-windows get the share loop's plain solve, then the threshold ladder (first test at T = min(ub, 108), 60 s limit).
- The oracle reads `../s0_share_loop/share_oracle.jsonl`, `../s0_k6_ceiling/oracle5_extra.jsonl` and the E1 seeds, and writes `oracle_share.jsonl`.

**Trend.**

| round | 0 | 10 | 20 | 30 | 40 | 50–79 | 90 | 98 |
|---|---|---|---|---|---|---|---|---|
| μ | 4.1053 | 4.1389 | 4.1538 | 4.1719 | 4.1852 | 4.2000 (plateau) | 4.2182 | **4.2222** |
| m ≤ | 234.52 | 234.32 | 234.23 | 234.12 | 234.04 | 233.95 | 233.85 | **233.82** |

- The bound gained about +0.012 per hour at the end.
- At round 0, the share charges lift the plain ceiling from 4.0625 to 4.105 at once.
- After that, 83 of the 99 minimum cycles had T5 = 0 on every edge, so progress comes almost entirely from **6-window plain exclusions**: 1,777 tests, 1,622 of them UNSAT. Only 281 threshold tests were needed (116 UNSAT, 55 timeouts).
- 233 needs μ ≈ 4.30 in the Lean chain. At the current rate that is more than 6 CPU-hours away, and it is not certain to be reached.

**Certificates.** At λ = 496 (μ = 4.133, enough for 234), `minimal.py B --lam 496` keeps:
- 2,426 plain exclusions;
- 564 share charges, meaning keys whose T5 is needed for non-negative slack.

At the reached λ = 1520/3, it keeps 3,161 plain exclusions and 565 share charges.

## Proof sizes (`proofs.py`, `sample_plain.py`, `sample_share.py`; `proof_samples.jsonl`)

The hints are trimmed CaDiCaL 2.1.3 LRAT, counting only the dependencies of the empty clause. Each proof was deleted right after counting.

| class | n | median hints | mean hints | max | CNF variables |
|---|---|---|---|---|---|
| A, 5-centre plain | 14 | 0.25 M | 1.17 M | 10.2 M | ≤ 3,484 |
| A, 6-centre plain | 10 | 1.13 M | 2.10 M | 10.6 M | **≤ 4,040** |
| B, share threshold (T = 107–108) | 6 | 2.2 M | ≥ 3.2 M (one proof exceeded the 120 MB cap) | > 8.6 M | ≈ 43,000 |

The share loop's 30 samples gave a median of 4.0 M and a mean of 6.6 M hints. The cost ranges in the Answer use median to mean per class, times the counts, plus the base keys not yet in the 236 replay set. Cost-aware pruning (`prune_costly.py`) usually removes the largest proofs on top of this.

## Lean-side consequences

1. **The plain k6 route gives 235 with no new proof machinery.** It needs:
   - a k6 version of `gen_lean_automaton5.py`/`DirectionWindowBridge5R4`, with one more count in the state and 6-window keys;
   - about 1.6k new plus up to about 1.7k base plain certificates;
   - checker offsets above 4,000, because the 6-window CNFs have up to 4,040 variables, just past `LratFastO4k*`.
2. **State count.**
   - The full product is 264,384 states, against 44,064 for k5.
   - Sharding by (shape, a0) gives 204 shards with exactly the size of today's 34 k5 shards, which is about 6 times the k5 automaton check.
   - Restricting the check to the 51k live states would need a closed-set argument in Lean.
3. **The share route (B)** reaches 234 solver-side, with 233 open and rising slowly. Its cost is about 3 times A, plus share clause soundness (stages 4–5).

**Recommendation.** Formalise (A) first: 236 → 235 for an estimated 110–430 kernel-hours, with only existing machinery. Keep (B) running solver-side as the path to 234.

## Files

| file | contents |
|---|---|
| `k6loop.py` | graph build (cache in the scratchpad), plain oracle, loops A/B, `evalA`/`evalB` |
| `minimal.py` | dual-pruning certificate count, exact potential and Lean arithmetic (`--target`, `--lam`) |
| `base.py` | upper bound on the base exclusions |
| `proofs.py`, `sample_plain.py`, `sample_share.py` | LRAT sampling |
| `oracle_plain.jsonl` | 2,942 plain calls (A, then the 6-window calls of B) |
| `oracle_share.jsonl` | 396 share-loop calls of B |
| `rounds_A.jsonl`, `rounds_B.jsonl`, `run*.log.gz` | checkpoints and logs |
| `minimal_*.json`, `base_*.json` | kept key lists |

To resume, rerun `k6loop.py B HOURS`.
