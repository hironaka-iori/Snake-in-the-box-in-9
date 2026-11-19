# Predicting a(9): heuristic evidence (NOT proof)

Everything in this file is heuristic. None of it bounds a(9). Proven: 191 <= a(9) <= 231 (Lean).

## (A) Cross-dimension calibration of the surgery annealer

Same binary (`bin/surgery`), same configuration `-b 4 -T0 0.65 -T1 0.65` (beta = 4, constant T = 0.65,
surgery dimension uniform in {2,3,4}), one core. Q7: 40 seeds x 20 s. Q8: 30 seeds x 120 s.
Q9: the 10-minute calibration runs and the first 30-minute 192-search runs (several configurations of
the same family). Rates are censored exponential estimates (`src/rates.py`):
rate(L) = (#runs reaching >= L) / (total time until first hit or end of run).

| Q_n | L (edges) | runs hit | rate per core-hour | ratio rate(L-1)/rate(L) |
|---|---|---|---|---|
| Q7 (opt 50) | 50 | 40/40 | 5.7e3 | 2.1 |
| | 49 | 40/40 | 1.2e4 | 5.0 |
| | 48 | 40/40 | 6.1e4 | 8.7 |
| Q8 (opt 98) | 98 | 13/30 | 17.5 | 4.3 |
| | 97 | 26/30 | 75 | 1.5 |
| | 96 | 27/30 | 113 | 5.5 |
| | 95 | 30/30 | 619 | 2.3 |
| Q9 (opt ?) | 191 | 2/14 finished runs (+1 in a run stopped at ~870 s) | 0.48 (about 0.6 with the stopped run) | 21 |
| | 190 | 11/14 | 10 | 1.9 |
| | 189 | 13/14 | 19 | |

Observations.
- The step ratio rate(L-1)/rate(L) near the top alternates in Q8 (4.3, 1.5, 5.5, 2.3), i.e. odd/even
  effects are as large as the trend. One step ratio is not a reliable discriminator.
- In Q9 the last observed step, 190 -> 191, costs a factor ~21 (2-3 hits, so the 95% range is roughly
  6-80). This is much steeper than the steps at the optimum in Q7 (2.1) and Q8 (4.3) and than any
  sub-optimal step seen in Q7/Q8 (<= 8.7).
- Hypothesis "a(9) = 191": the Q9 top step (21) would be the "opt" step; it continues the increasing
  trend 2.1 (Q7) -> 4.3 (Q8) -> 21 (Q9) of a dimension-growing barrier at the optimum. Plausible.
- Hypotheses "a(9) >= 192": 191 would be opt-1 (or lower). In Q7/Q8, sub-optimal steps cost at most
  a factor ~9, so a factor 21 at a sub-optimal level is unusual but within the large Q9 error bar.
  If the next step 191 -> 192 cost a Q8-like factor 2-6, a 192 would appear at 0.1-0.3 per core-hour,
  i.e. within ~10-30 core-hours of this search. If it cost a factor like 21, at ~0.03/h (~35 core-hours).
  Each further level (193, 194, 196) multiplies the required time by a similar factor.
- Likelihood-style reading: an observation of 0 hits at 192 over T core-hours has likelihood
  exp(-r192 T) under "192 exists". After the 192 search (~3 cores x many hours) this is quantified
  in section (A2) below.
- Ranking from (A) alone (weak): 191 >= 192 > 193 > 194 > 196 in plausibility, mostly because each
  hypothesis above 192 requires the Q9 rate curve to bend back after an unusually steep step.
  Sensitivity: high. With 2-3 hits at 191 the step ratio is known only to a factor ~4 either way, and
  the annealer is a biased sampler (basins, bank re-discovery), not a uniform one.
- Additional signal: all 191-edge snakes found so far are equivalent to entries of the existing
  131-entry bank (`work/bank9.json`, canonical transition-sequence form). The search re-discovers
  the same plateau rather than finding new 191s, which also suggests the 191 level is close to
  the top of what this landscape offers (again heuristic).

## (A2) 192 search exposure

(updated as the search runs)

## (B) Density of states (Wang-Landau)

(pending)

## (C) Inequivalent snakes found per length

(pending)
