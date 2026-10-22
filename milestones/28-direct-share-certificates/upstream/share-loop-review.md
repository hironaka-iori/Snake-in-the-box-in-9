# The s0 share loop (stage 3 of `../s0_lean_design.md`), first production run

Run of 21 October 2026. It used about 3.9 h of wall time on one core at nice 19, alongside a Lean replay build. Everything here is solver-side: nothing is a Lean theorem yet. Units follow the design. M = 12, the edge weight is W(e) = 120·sym + T5(key5(e)), μ = λ/120, and the implied bound is m ≤ 9171/(μ+35), before the potential constant C of the Lean chain. The thresholds on μ are:

| m ≤ | 236 | 235 | 234 | 233 | 232 | 231 | 230 | 229 | 228 | 227 |
|---|---|---|---|---|---|---|---|---|---|---|
| μ > | 3.696 | 3.860 | 4.026 | 4.192 | 4.361 | 4.530 | 4.701 | 4.874 | 5.048 | 5.224 |

## Files

- `wincert_share.py` is the production encoding of `../s0_lean_design.md` §4.1. `ShareEncoding(window, alpha, radius, M, cap)` is `wincert.Encoding`, unchanged, followed by these clauses:
  - `emptyE`, `totUp`/`totDown` (the e0 and d totalizers) and `shareCl`;
  - a static cap totalizer truncated at cap+1;
  - the unit `shareCap`.

  Cycle cuts are lazy, as in `wincert.decide`. The truncated totalizer emits `o[i+j] <- a[i] & b[j]` only for i+j ≤ cap+1. That is complete for "≥ cap+1", so the `totUp` tag of §4.2 needs no change. `measure_proof` runs the CaDiCaL 2.1.3 binary twice: once for DRAT size, then with `--lrat`, trimmed by `gen_lean_core.trim_lrat` to the empty clause's dependencies. It deletes every proof file right after measuring it.
- `refine_share.py` is the loop of §4.3, on the radius-4 L7 k5 K5 automaton: 44,064 states, 240,729 edges and 11,425 distinct 5-window keys, with the exclusions of the radius-4 oracle cache. Each round evaluates two automata, each with Howard, giving two exact means:
  - **lo (rigorous):** T5 = proved lower bound, and 0 when a window is untested or timed out.
  - **hi (rigorous ceiling):** T5 = best SAT witness, and +∞ when untested. No set of 5-window share certificates can lift this automaton above μ_hi.

  Each window on both minimum cycles then gets one test. The first visit is a plain solve: UNSAT gives a new plain exclusion, and SAT gives a witness, which is an upper bound. The visit then runs a threshold test at T = min(ub, 108). Later visits step up the ladder 150/200/…, or back off below a level that timed out. The time limit is 60 s per call. The loop resumes from `share_oracle.jsonl`, which has one line per solver call, and it also reads the E1 results of `../s0_radius4/` as seeds.
- `summarize.py` writes `summary.json`. It contains the counts, the proof samples, the cost estimate and non-rigorous what-if means.
- The data files are `rounds.jsonl` (one checkpoint per round), `share_oracle.jsonl` (2,003 solver calls) and `loop.log.gz`.

## Results

**Progress.** The table shows (round, time, μ_lo, μ_hi) for 114 rounds:

| round | 0 | 16 | 24 | 32–72 | 80 | 96 | 113 |
|---|---|---|---|---|---|---|---|
| μ_lo | 3.875 | 3.933 | 3.968 | 4.000 (plateau) | 4.024 | 4.069 | **4.1034** (m ≤ 234.53) |
| μ_hi | 5.165 | 5.153 | 4.963 | 4.963 → 4.719 | 4.719 | 4.719 | **4.7194** (m ≤ 230.89) |

- **Rigorous solver-side bound: m ≤ 234** (λ = 14280/29). This is about 1.4 edges beyond 236, and it was still rising at about 0.0013 per round, roughly +0.005 per CPU-hour of tests.
- In every round the rigorous minimum cycle consisted entirely of untested windows (T5 = 0). This is the 170-round pattern of the original refinement, with about 11k keys to cover.

**The ceiling is rigorous: μ ≤ 4.7194, so this route cannot do better than 230 edges.** The optimistic minimum cycle is a period-3 cycle with all counts α = 4. Its windows are:

| window key | α | share |
|---|---|---|
| (0,1,2,3,0,4) | 4,4,4,4,4 | proved exactly 94 (lb = ub) |
| (0,1,2,3,0,4), second edge | 4,4,4,4,4 | 94 |
| (0,1,2,3,0,1) | 4,4,4,4,4 | witness 71; timed out even at T = 24 |

So μ_hi = 4 + (94 + 94 + 71)/360 = 4.7194. Some further points:

- 230 would need μ > 4.7013. That is 0.018 of slack, before the potential constant (0.3–1.3 edges at 14–16 bits, §3.2).
- A larger symbol cap does not move this cycle, because it has no symbol 6.
- 229 and below are out of reach for L7 k5 radius-4 5-window shares at M = 12.

**What-if estimates (not rigorous).** Tested windows take a value up to their witness; untested windows are assumed to force F.

| F | 48 | 72 | 85 | ≥ 96 |
|---|---|---|---|---|
| μ | 4.40 | 4.60 | 4.6945 | 4.7194, the ceiling |
| m ≤ | 232.8 | 231.6 | 231.04 | 230.9 |

For comparison, 108 is the typical forced value: 382 of the 623 decided threshold tests were UNSAT (380 keys hold lb = 108), and the SAT witnesses lay mostly between 82 and 106. If the tested windows instead keep only their proved lb, the mean sticks at **4.133 (234.35)** for every F. Two hard period-3 windows bind there:

- (0,1,2,3,0,1) with α 3,3,6,3,3: witness 88, timed out at T = 24;
- (0,1,2,3,0,4) with α 3,6,3,3,6: lb 24, witness 95, timed out at 95.

**Answer to "231, 233 or lower?"** The weighted mean converges to about 4.69–4.72, which is **231 edges, with 230 possible only with zero slack**. It does not converge to 233. This requires two things:
- every untested window forces about 85 or more;
- the hard α = 3/4 period-3 windows are proved near their witnesses, which takes solves far longer than 60 s.

**Certificates and solver times.**
- Calls made:
  - 1,320 plain calls: 831 UNSAT, 481 SAT and 8 timeouts;
  - 683 threshold calls: 382 UNSAT, 241 SAT and 60 timeouts.
- Threshold solve times were 7.7 s at the median, 56 s at p90 and 3.1 h in total.
- **The automaton currently uses 484 share windows (key, K)**: 380 at T = 108, 28 at 150, 20 at 24, and the rest exact minima between 72 and 301.
- It also uses **835 new plain exclusions**. These are radius-4 windows that the base refinement never queried; they solve in under 1 s and are cheap but not free in Lean.
- The CNFs have 34–43k variables and 350–535k clauses. That needs a checker offset of about 44000, not the 24000 the design assumed.

**Proof sizes.** There were 30 samples, all UNSAT at T = 82–108, with solves of 0.6–40 s:
- DRAT: 1.4–79 MB, 28.5 MB on average;
- trimmed LRAT: 0.34–18.8 M hints, median 4.0 M, mean 6.6 M. That is roughly 0.5 M hints per solver-second;
- UNSAT cores: 7–40k clauses;
- drat-trim verified the one sample that was checked (the smoke test, which is not in the oracle file).

## Cost estimate

The basis is the 237 rate: 34 kernel-h for 289 M hints, or 0.42 ms per hint.

| set | certificates | hints | kernel-hours |
|---|---|---|---|
| current 484 | 484 | 3.2 G | about **370** (230 at the median) |
| a converged set | 3,000–6,000, extrapolating from the lo cycle still being all untested after 1,461 tested keys | 20–40 G | **1,000–2,500**, before shrinking |
| after core re-solving and a lower K | same | –30 to –50% (portfolio); 72 or 85 instead of 108 should cut more (unmeasured) | ≥ 500–1,500 |

The current set's size also rules out the replay-checker offset of 4000. The hard binding windows will produce some of the largest proofs.

## Recommended next step

Do not start the Lean stages 4–5 on this automaton yet. The ceiling caps the reward at 230–231, and the replay cost is 30–70 times that of 237. First, cheaply and solver-side:
1. Settle the period-3 obstruction. Run long single solves (one core, ≥ 1 h each) on the three ceiling windows and the two lo-binding windows; the ceiling cannot be lowered or the lo plateau lifted otherwise.
2. Re-run the loop with a lower ladder (72 or 85 first) and measure hints against T. 231 needs only an average T5 of about 85.
3. For 227–230, the period-3 all-α=4 cycle must be killed outright, not charged. That means k = 6 windows or L = 8 states, or exact M = 2520 shares on those windows. Test those three windows first: if they stay SAT at k = 6 or radius 5, the local share method stops at about 230.
