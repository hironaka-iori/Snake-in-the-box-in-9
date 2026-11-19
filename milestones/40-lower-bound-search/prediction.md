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

About 13.5 core-hours of Q9 surgery annealing up to 19:00-21:00 UTC (10-minute restarts after the
first 4.5 hours; one third of the later runs started from bank 191 snakes). 0 hits at 192.
Bank-start runs never left the 191 level upwards. Fresh-start runs: 3 hits at 191 in total.

## (B) Density of states (Wang-Landau)

`src/wl.c`: Wang-Landau on directed snakes with end moves only (add or delete a vertex at either end,
Metropolis-Hastings corrected), normalised by N(0) = 2^n. Validation against exact enumeration
(`src/enum_exact.py`): Q4 within 0.005 and Q5 within 0.003 in ln N at every length. Runs (one core):
Q5 120 s, Q6 900 s, Q7 1800 s, Q8 2400 s, Q9 2400 s. Converged range (final ln f): Q6 up to 25 of 26
(5e-7), Q7 up to 46 of 50 (1e-6), Q8 up to ~79 of 98 (6e-5; bins 80-83 are unconverged),
Q9 up to 142 (2.4e-4, not well converged). Data: `results/wl*.txt`.

Criterion: the maximum is where ln N(L) falls to ln(2^n n!), the size of one free orbit.

Method 1, polynomial extrapolation of S(L) = ln N(L) from the peak to a cut-off, then solving for
the crossing (`src/extrap.py`). Validation with the cut at 75% of the known optimum (the Q9 data end
at 143/191 = 75%): degree 2 gives Q7 54.6 (opt 50, +9%), Q8 108 (opt 98, +10%); degree 3 gives
Q7 54.2 (+8%), Q8 92.7 (-5%); Q5, Q6 and lower cut-offs often give no crossing. Q9: degree 3 gives
194 (cut 135) or 166 (cut 142), degree 2 gives 214 (cut 142). The method is unstable at the
+-10% level, i.e. +-20 edges in Q9. It cannot separate 191 from 192.

Method 2, ratio opt / L_peak (L_peak = most numerous length): Q5 13/10 = 1.30, Q6 26/18 = 1.44,
Q7 50/32 = 1.56, Q8 98/60 = 1.63. Q9: L_peak about 124 (flat 124-134 and not fully converged).
Continuing the slowing trend (+0.14, +0.12, +0.07, then +0.03 to +0.07) gives ratio 1.66-1.70 and
a(9) about 206-211 for L_peak = 124, or 191-196 if the true peak is at 115 (where L_peak/2^n would
continue its decreasing trend 0.313, 0.281, 0.250, 0.234). The L_peak uncertainty alone moves
the prediction by about 15 edges.

Conclusion (B): the density-of-states extrapolation predicts a(9) in roughly 190-215, centred
somewhat above 191, with an error bar (from the Q7/Q8 validation) of about +-10%. It does not
discriminate between 191, 192, 193 or 194. Better convergence near the top in Q8 and Q9 would need
moves other than end moves (e.g. surgery moves with a proper reverse-move probability).

## (C) Inequivalent snakes found per length

Canonical form: transition sequence with coordinates relabelled in order of first use, minimised over
both directions (`src/canon.py`). Counts are of improvement records only (each run logs a length the
first time it reaches it), so they are biased toward the first snake found per run.

| | opt-5 | opt-4 | opt-3 | opt-2 | opt-1 | opt |
|---|---|---|---|---|---|---|
| Q8 (opt 98), 30 runs | 93: 23 | 94: 26 | 95: 27 | 96: 20 | 97: 15 | 98: **1 class in 13 hits** |

| Q9 | 188 | 189 | 190 | 191 |
|---|---|---|---|---|
| classes (hits) | 35 (35) | 25 (25) | 39 (50) | 3 (3), all in the 131-entry bank |

Reading: in Q8 every one of the 13 hits at the optimum is the same class. The Q9 top level behaves
differently: 3 hits gave 3 different classes, and the bank already holds 131 inequivalent 191s.
A large, diverse top plateau looks more like Q8's opt-1 level (15 classes in 26 hits) than like its
optimum. This is the one signal that points toward a(9) > 191, but it rests on one comparison
dimension and on biased sampling, so it is weak.

## Overall (heuristic)

(A) favours 191 weakly (steep last step); (B) is centred a little above 191 but uncertain by +-20;
(C) favours a(9) > 191 weakly (diverse top plateau). Together: no method here separates 191 from 192.

