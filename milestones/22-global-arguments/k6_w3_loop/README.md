# k6 refinement loop with six-centre w_3 weights

Run of 21 October 2026, 15:20–19:35 (about 4.2 h of solver time on one core at nice 19, next to a Lean build; solves one at a time). **Everything here is solver-side. Nothing is a Lean theorem, and no bound in the chain changes.**

Units are those of `../w3_survey` and `../k6_w3`: c(x) = Σ_Q ⌊12/|Q∩S|⌋, μ = per-vertex mean of c, m ≤ 7 + 63148/μ (the k = 6 boundary terms are not re-derived; they move m by < 0.1). 230 needs μ > 281.9, 228 needs μ > 285.

## Answer

| | value | graph | status |
|---|---|---|---|
| **rigorous lower side** | λ6 = 1630, **μ = 271.67, m ≤ 239.45** | full product (264,384 states, `fullprod.py`) **and** lifted live graph (same value) | solver-side; exact integer potential found (Bellman-Ford, 23 rounds) |
| start of the run (T5 weights, `../k6_w3`) | μ = 271.06 (m ≤ 239.96) | lifted | |
| trend | +0.6 μ in 4 h: 271.19 → 271.50 (1.2 h) → 271.61 (2.3 h) → 271.63 (3.8 h) → 271.67; **slowing**, about +0.05 μ/h at the end | lifted | |
| **ceiling** (lowest cycle whose every 6-window has a SAT witness) | λ6 = 5282/3, **μ = 293.44, m ≤ 222.2** (the period-6 cycle of `../k6_w3`, exact minima 1744/1769/1769) | full product **and** lifted (14 witnessed live transitions) | rigorous as a ceiling |
| 230 (μ ≈ 282) / 228 (μ ≈ 285) reached? | **No, neither.** The lower side is 10.3 c per vertex short of 230. | | |

## Which graph each number refers to

The coordinator's warning (milestone 23: the k6_loop A set gives 65/16 on the lifted graph but 31/8 on the full product) applies to *key subsets*, not to the loop's own evaluation:

- The loop runs on the lifted live graph of the k5 pickle (`../../11-local-ceiling/k6_loop`). That pickle already omits every edge whose window the radius-4 oracle cache knew to be UNSAT.
- `fullprod.py` recomputes the minimum on the **full product that the Lean k6 check enumerates** (`../../23-k6-lean/scripts/gen_lean_automaton6.py`: `shapes7`, `build_tables`, `transitions`), with **every** known plain-UNSAT key with lumped counts as an exclusion (27,571 keys, 24,323 of them six-centre; 5,428 keys with non-lumped ranges are left out, which can only lower the minimum) and the same W6 weights on dense tables over all count tuples.
- Both graphs give λ6 = 1630. The witnessed ceiling cycle also lives in both.
- The certificate count below (`prune.py`) is a dual pruning **on the lifted graph**. Exactly as for k6_loop A, a subset chosen there need not hold on the full product; it has to be re-pruned on the full product before any Lean use.

## Method (`k6w3loop.py`)

- **Weight of a k6 edge** = a certified lower bound on the w_3 charge of its 6-window:
  W6 = max(lb6, lb5(left 5) + s(α_6), s(α_1) + lb5(right 5)).
  lb6/lb5 are threshold-SAT results with the w3_survey encoding and symmetry breaking; lb5 includes the sub-window DP floor of `refine_w3.Sub`; s(α) are the single-centre minima (257–279). Every internal vertex lies in 6 consecutive 6-windows, so μ = λ6/6.
- **Each round**: Howard's minimum cycle; then (1) plain tests of the cycle's untested 6-windows and of the 1,500 lowest-W6 untested live 6-keys ("bulk"), (2) only if the cycle has no untested key: thresholds on the cycle, target ⌈λ6⌉ + 12, cheapest option first (one 5-sub-window at need, need+10, … while each step is under 8 s; otherwise the 6-window ladder).
- **Range plain tests**: untested 6-keys that share directions and the last five counts are first tested together, with the first count as the hull range. UNSAT excludes all of them (one certificate per group); SAT or timeout falls back to single keys.
- Every call is logged (`data/plain_loop.jsonl.gz`, `data/w3_loop_oracle.jsonl`), every round checkpointed (`data/rounds.jsonl`).

## What happened

1. **The binding cycles are plain-infeasible, not charge-bound.** Of the 6-windows on the minimum cycles and in the bulk sweep, about 97 % were plain-UNSAT. 21,459 six-centre keys were excluded (7,105 single tests, 14,354 via 4,139 range tests; 323 SAT). The live lifted graph shrank from 727 k to 542 k edges.
2. **There are too many keys at the floor.** When the run started, 93.7 k of the 97.9 k live 6-keys had W6 < 1692 (that is μ < 282), and 98 % were untested. At the end, 33.5 k untested keys still lay below λ6 + 12. The weights are flat (1619–1640), so each round lifts λ6 by about 1/6 c.
3. **Thresholds are not the bottleneck yet.** Only 47 w_3 calls were needed: 6-window thresholds at 1640–1680 were UNSAT in 0.1–21 s. The 5-window thresholds at 1360–1380 on the low-α keys (3,4,4,3,·) timed out at 60 s in 19 of 37 cases.
4. **α-range keys do not help on the w_3 side.** `012304` with every α ≥ 3 at T = 1340 (floor 1335) timed out after 240 s.
5. **Extrapolation.** Clearing the remaining 33 k keys below λ6 + 12 costs about 4–6 h of plain tests and buys at most +2 μ. Reaching μ ≈ 282 needs almost every one of the ~94 k live 6-keys below 1692 excluded or certified, which is tens of CPU-hours of plain tests plus thousands of threshold tests. So **230 is out of reach for this route at this rate**, even though its ceiling (222.2) is far below.

## Certificates and cost

- **LRAT samples** (`data/proof_samples.jsonl`, CaDiCaL 2.1.3 `--lrat`, trimmed, deleted):
  - 6-window thresholds at T = 1640: 59 k, 94 k, 0.46 M and 2.29 M hints, plus one over the 90 MB raw cap (about 3 M or more). That is a median of about 0.5 M and a mean of about 1.2 M or more.
  - The raw LRAT of a 6-window CNF (49 k variables, 2.3 M clauses, 55 MB) is 28–94 MB, so 7 samples hit the first run's 45 MB cap.
  - One 5-window at 1370: 1.65 M hints.
  - Plain 6-window exclusions: use k6_loop's figures (median 1.13 M, mean 2.10 M hints). Range certificates were not sampled.
- **Cost-aware pruning** (`prune.py`, dual pruning on the lifted graph, fixed potential): **m ≤ 239** (μ* = 271.02) needs 16 five-window and 11 six-window thresholds (about 34 M hints, about 4 kernel-hours) plus **3,268 plain 6-window exclusions**, 2,900 of them new in this run. At 1.1–2.1 M hints each, the exclusions cost about **430–800 kernel-hours** (0.42 ms per hint), plus the base exclusions and the sub-window and single-centre certificates.
  - 238 is not reachable (μ* = 272.19).
  - The 236 chain already exists, so this set has no Lean value.

## Recommendation

**Do not formalise k6 + w_3.** Its rigorous lower side (239.4) is worse than the existing 236 chain. Its certificate count, dominated by 6-window plain exclusions, is in the thousands, and it grows with every 0.1 of μ. 230 would need about 10^5 window certificates.

The route's value is its ceiling (222.2 on the one fully witnessed cycle), not anything provable at present.

If it is pursued, the first job is a fast plain 6-window sweep, a C or batch encoder, since today's cost is 0.4–0.8 s per key. It should run on the full product. Threshold work only matters after that.

For Lean in the near term, keep the plain k6 route, re-pruned on the full product (milestone 23).

## Incidents

- From 15:40 to 15:50 a probe solve (`α ≥ 3` range test, `bench`) overlapped the loop: `kill -STOP` hit the nohup shell, not the Python child. This was one extra single-threaded solver for about 10 min. Later pauses used the Python PID.
- The first 15 minutes of output went to `../k6_w3/data` because of a name clash (`HERE`). The files were moved here, and `../k6_w3` is unchanged.

## Files

| file | contents |
|---|---|
| `k6w3loop.py` | the loop (W6 tables, bulk and range plain tests, threshold ladders, LRAT sampling); `python k6w3loop.py HOURS [DELTA] [SAMPLE]` |
| `fullprod.py` | minimum cycle, exact potential and ceiling on the Lean full product (`data/fullprod.json`) |
| `prune.py` | cost-aware certificate count per target bound (`data/prune.json`) |
| `sweep6.py`, `fastplain.py`, `control6.py` | per-shape incremental 6-window solvers. The control agreed on 299 of 300 known keys (1 timeout, `data/control6.json`), but it was not faster than fresh small CNFs (0.6–1.1 s per key), so it was not used in the loop |
| `thrsample.py`, `lratsample.py` | 6-window thresholds on the lowest plain-SAT keys, and LRAT measurement (90 MB raw cap; CNF deleted before trimming) |
| `data/rounds.jsonl` | 33 rounds: λ6, μ, m, cycle keys and weights, live edges; every 10th round also μ5 and the ceiling |
| `data/plain_loop.jsonl.gz` | 28 k plain records (`plain`, `plainrange`, derived `src: range`) |
| `data/w3_loop_oracle.jsonl` | w_3 threshold calls (w3survey record format) |
| `data/proof_samples.jsonl`, `data/thrsample.log`, `data/run.log.gz` | samples and logs |
