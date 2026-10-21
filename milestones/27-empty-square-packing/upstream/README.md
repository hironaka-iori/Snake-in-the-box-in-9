# The s0 corner share at radius 4 (experiment E1, 19 October 2026)

Question: how much can the empty-square share (the corner rule of
`../s0_corner_charge.md`) raise the per-vertex lower bound of the radius-4 window
automaton (mean 42/11, which gives 236)?  Everything below is a SAT computation in the
local window model (pysat CaDiCaL 1.5.3); nothing here is a Lean theorem, and the global
estimates at the end are not rigorous.

## Model and units

`wincert.Encoding` at radius 4 with lazy cycle cuts, plus for the 28 squares through each
unselected neighbour q of a centre an indicator `E[q,ij] <- square empty`, totalizers for
e0(q) (up) and d(q) (down), and `u[q,t] <- (e0 >= ceil(t dd / M)) and (d <= dd)`; then
`sum u >= shareN = sum_q floor(M e0(q) / d(q))`, so UNSAT of `sum u <= K` proves
`shareN >= K + 1` in the local model (`e1lib.py`).  SAT witnesses are recomputed exactly.

Per-vertex charge gamma = alpha + shareN / (2M), matching
`sum (4M alpha + 2 shareN) <= M (36856 - 140 v)`, so `v <= 9214 / (35 + mu)`: 230 edges
needs mu > 4.716, 231 needs mu > 4.676.  M = 2 is useless (every share rounds to 0); M = 12
is exact for d in {1,2,3,4,6}, M = 2520 for all d.  A Lean version needs M >= 12.

## Results

**Single centre** (`single.py`, `single_*.json`): proved minimum share 4/15 (alpha = 1),
3/20 (alpha = 2), >= 1/24 (alpha = 3), exactly 0 (alpha = 5); witnesses 1/7 (alpha = 4),
1/14 (alpha >= 6).  Even with witness values the automaton only moves to 9911/2520 = 3.933
(v <= 236.66): about one edge.

**Two and three centres** (`window.py`, `windows_results.jsonl`): e.g. (2,2), (2,4): exactly
10/24; (1,5): 23/24; (2,6+,2): 25/24; (2,2,6+): 39/24 (proved optima, M = 12).  Re-weighted
automata reach 3.87-4.0, still about 236.

**Five-centre windows** (the automaton's own k = 5 windows; `ceiling.py`, `threshold.py`,
`ceiling_results.jsonl`, `threshold_results.jsonl`): here the share is large.  Proved
optima include 292, 244, 245, 163, 120, 131 (shareN, M = 12) on windows of the minimum
cycles.  Threshold tests on 166 windows from successive minimum cycles: 114 proved
shareN >= 108 (0.9 per vertex), 25 more proved >= 150, 13 timed out, 14 SAT below the
threshold with witnesses 88-148.

**Predicted bound** (`refine_share.py`, `estimate.py`, `refshare_results.jsonl`):

| what | mean mu | consequence | status |
|---|---|---|---|
| 42/11 cycle with its 5-window lower bounds | >= 5.25 | | proved for that cycle only |
| [2,3,6,3,3,6] cycle | >= 4.81 | | proved for that cycle only |
| share-aware refinement, 8 rounds | 3.89 -> 3.93 | | rigorous given the cache, far from converged |
| untested windows assumed to force 108 / 150 | 4.76 / 4.77 | v <= 231, i.e. 230 edges | not rigorous |
| untested windows assumed to force 88 / 74 | 4.61 / 4.49 | 231 / 232 edges | not rigorous |

**Conclusion:** single, pair and triple windows give about 233-236; five-centre radius-4
windows with the share plausibly reach 231, and 230 only barely.  Settling it needs a full
share-aware refinement (the original took about 170 rounds), exact window minima instead
of threshold tests, probably a larger symbol cap (the lumped 6+ hides alpha = 7-11), and
M >= 12 in Lean.

`automaton.py` rebuilds its 43 MB cache `aut_L7k5K5r4.pkl` (not committed) from the
radius-4 oracle cache; it reproduces 42/11.
