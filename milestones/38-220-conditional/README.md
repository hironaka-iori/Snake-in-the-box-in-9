# Milestone 38: is a conditional bound near 220 feasible? (track A: the K7 window-automaton route)

Run of 18 November 2026 on one 4-core, 15 GB machine. Track B's study of other directions is in
[`trackB.md`](trackB.md). **No bound is claimed here.** The Lean result of this milestone is a
*conditional* theorem; its share premise is not certified, and for the levels above 60 it is not
even known to be true.

## Answer

1. **A conditional bound of 220 (or anything <= 222) is not feasible with premises of the existing
   kinds** (plain window exclusions `Refuted (winOf dirs) bounds` and corner-share thresholds
   `RefutedShare (winOf dirs) bounds 12 K` on windows of at most 7 centres).
   - Every 7-centre data type is capped by validated local models: the uniform share floor at
     **226** (a CNF-validated model of shape `0,1,2,3,0,1,4,0` has corner share 165; this run),
     the uniform combined floor at 225 and the shape-only automaton at 221 (track B), the k6
     share type at 223.5 (milestone 28).
   - Far above those caps, the proof cost is already prohibitive: see "Cost" below. Each unit of
     bound below 230 costs roughly 10 to 30 times the certificate work of the previous one.
   - Longer windows are the only lever that the ceilings leave open, and no count automaton with
     more than 7 centres is of tractable size (see "Longer windows").
2. **The best feasible candidate is 229**, by the 230 machinery with the uniform 7-window
   corner-share floor raised from 30 to **60**. Its window premise is *the same table* `tab230`
   that the 230 farm is certifying; only the 132 share certificates change (level 60 instead of 30).
   - Truth: a stratified sample of 14 shapes was tested at level 60 with CaDiCaL; 7 are UNSAT
     (4 to 740 s) and 7 timed out at 900 s. No SAT answer at any level up to 81 on any of the
     132 shapes; the lowest validated witness has share 165.
   - Cost: of order 1,000-4,000 G replay hints for the 132 share keys if the measured growth holds,
     against about 80 G for the whole 230 plan; the hard shapes would need count-splitting. See "Cost".
3. **Lean:** `Snake9.upper_229_of_refutedK7 : AllTab tab230 → AllShareK 59 shares230 → ∀ {m}, Snake m → m ≤ 229`
   (Lean 4.35, `lean435/c229/C229Final.lean`), an instance of the parametrised count
   `Snake9.upper_of_refutedK7_share`. Status of the build and audit: see "Lean".

## The parametrised count (`trackA/bounds.py`, `lean435/c229/C229Final.lean`)

With the K7 walk `89 m <= 19 Σ_{k=1}^{m-1} α_k + 678` (premise `AllTab tab230`), the corner identity
`Σ_{k<=m} (24 α_k + share_k) + 840 (m+1) <= 221136`, `α_0, α_m >= 4`, and a uniform floor X on the
corner share of the 7 centres of each of the `m - 7` windows:

    (126672 + 19 X) m <= 29387736 + 133 X.

| bound | least X | per vertex `24 α + share` |
|---|---|---|
| 230 | 30 | 116.7 |
| 229 | 60 | 121.0 |
| 228 | 91 | 125.4 |
| 227 | 121 | 129.7 |
| 226 | 152 | 134.1 |
| 225 | 183 | 138.6 |
| 224 | 215 | 143.1 |
| 222 | 278 | 152.1 |
| 220 | 343 | 161.4 |

(Track B's table uses `m - 8` windows and gives 61 for 229; the Lean count has `m - 7` windows.)
Witnessed ceiling: X <= 165 (`trackA/data/sharemin.jsonl`, CP-SAT model hinted with track B's
167-witness, re-validated as a model of the `wincert.Encoding` CNF), and X <= 243 on real snakes.
So the uniform route ends at 226 whatever is proved.

## What was computed (all solver or exact-arithmetic evidence)

The K7R34C7W16 product was rebuilt from the 58,817-key table with the relaxed-keller tools
(`lean_automaton.py`, `lean_minimize.py`, C Howard; scripts `lpsym.py`, `lpshape.py` here):
34,603,008 states, 563,584,123 edges, 180,971,992 after pruning, minimum cycle mean 75/16 (the
chain's 89/19 is the start-bounded potential). Units below: `24 α + share` per vertex (the window weight
`168 α + share` divided by 7); the baseline with X = 30 is 1635/14 = 116.8 and 229 needs about 121.5.

| candidate | premises | exact LP value | verdict |
|---|---|---|---|
| uniform floor X (free counts) | tab230 + 132 share keys at X - 1 | 112.5 + X/7 | 229 at X = 60; capped at 226 (X <= 165) |
| count-tiered floor: share >= X1 only on windows with all 7 counts <= c0 (exact by a symbol penalty `24 s - (X1 - 30) [s > c0]` on the same chain) | tab230 + 132 keys with bounds `[(1, c0)] x 7` (+ the 132 free keys at 29) | at X1 = 61, per vertex: c0 = 6: 1103/11 + 61/7 = 109.0; c0 = 7: 107 + 61/7 = 115.7; c0 = 5: 375/4 + 61/7 = 102.5 (baseline 116.8, 229 needs 121.5) | **a loss**: cycles such as `1,7,2,7,7,2,7,1,7,7,7` are alive in the table and bind at once; even a penalty of 4 at c0 = 6 lowers the mean (112.5 → 112) |
| per-shape floors X(s) as edge weights (the largest level proved in 40 s per shape) | tab230 + 132 keys at per-shape levels | 1635/14 = 116.8, unchanged | **no gain**: the binding count cycle `5,5,4,4,4,6,6,3,5,6,4,4,4,5,5,5` has a realisation on shapes whose floor stays at 30 |
| count-dependent floors on the chain's states (share-weighted K7 chain) | tab230 + one share key per binding (shape, counts) | not computable without an oracle for 34.6 M states; sampled below | needs tens of thousands of hard share keys per unit; no Lean generator (the SWAR chain takes weights that depend on the new symbol only) |
| more K7 plain windows (alpha only) | larger table | 229 needs mean 4.882 at X = 30 | the relaxed-keller refinement needed about 7,900 new windows for 131/28 → 89/19 (+0.0056); +0.2 is out of reach |

Measurements behind the table:

- **Per-shape free-count ladder** (`trackA/ladder7.py`, `data/shapes_free_ladder.jsonl`; levels 31, 46,
  61, 81, 101, ...; 40 s per level, 2 workers beside a Lean build): the largest level proved is below
  31 for 20 shapes, 31 for 48, 46 for 40, 61 for 20 and 81 for 4. No SAT answer.
- **Level 60, free counts, 900 s limit** (`data/free7_levels.jsonl`; 14 shapes, one per stratum of the
  solve time at level 30, `data/sample60_shapes.jsonl`). Level-30 time → level-60 result: 0 s → 4.2 s,
  0.1 → 4.8, 0.1 → 16.0, 0.2 → 329, 0.3 → TIMEOUT, 0.4 → 637, 1.3 → 258, 2.0 → 740, and TIMEOUT at
  900 s for the six shapes of 3.9, 8.6, 22.2, 49.5, 119 and 316 s. (The first seven ran 2 at a time
  beside a Lean build, the last seven 4 at a time.)
- **Count-fixed floors on the binding cycle** (`data/cycle0_ladder.jsonl`): for the 16 windows of
  the minimum cycle (counts fixed, lumped 8 = [8, 21]), the largest level proved in 40 s is 31 for
  3 windows, 46 for 11 and 81 for 2; level 61 times out on 11 of them. 229 needs +30 per window on
  *every* near-binding window, 225 needs +153 and 222 about +250.
- **Level 150, free counts**: TIMEOUT at 90 s on the two shapes tried, neither SAT nor UNSAT.
- **Count-tiered test** `[(1, 6)] x 7` at level 61: TIMEOUT at 120 s on the first shape; with the
  LP loss above this was not pursued.

## Truth check of the 229 candidate

Key set: the 58,817 windows of `tab230` (all already solver-refuted and DRAT-checked on the
relaxed-keller line; 33,628 are being certified by the 230 farm and 25,189 follow from 231
certificates) plus 132 share keys `RefutedShare (winOf s) [(1,21)] x 7 12 59`.

- The window part needs no new truth check.
- Share keys: there are only 132, so "a few hundred" could not be sampled. A stratified sample of
  14 (by solve time at level 30) ran with a 900 s limit: 7 UNSAT, 7 TIMEOUT, 0 SAT. In the 40 s
  ladder, 24 of the 132 shapes are UNSAT at level 61. **No key came out SAT**, and the lowest known
  model (165) is far above 60, but about 100 of the 132 keys have no answer at level 60 (every
  sampled shape that needs more than 2 s at level 30 timed out). The premise is plausible, not
  established.

## Cost

Calibration: about 1 M trimmed LRAT hints per CaDiCaL second for share thresholds (milestone 28),
kernel 0.3-0.5 ms per hint for share certificates (milestone 36).

- The 132 share keys at level 30 took 2,328 s in all (median 1.2 s, max 316 s).
- At level 60 the seven shapes that finished took 50 to 1,600 times their level-30 time (median
  about 370); the seven that timed out give only lower bounds (3 to 3,000 times). If the factor of
  the finished shapes (300-1,600) holds for the whole set, the 132 keys need 0.7-3.7 × 10^6 solver
  seconds, i.e. **of order 1,000-4,000 G hints**, against about 80 G for the whole 230 plan. The
  hard half of the shapes is unmeasured, so this is not an upper estimate.
- The distribution is the real obstacle: the shapes that take 100-316 s at level 30 would be single
  proofs of 10^11 hints or more, far above the 60 M cap of one certificate and beyond the split
  route. They would have to be split by counts (one certificate per count box and a cover lemma),
  which is new glue.
- **228** (level 91) and below: no shape reached level 101 in 40 s and only 4 reached 81; no
  estimate is possible beyond "at least another factor of 10 to 100".

### Count-split prototype (negative)

`trackA/split7.py` splits a level-60 key adaptively by counts: a box that CaDiCaL does not refute in
20 s is split on its widest centre (`[lo, 4] | [5, hi]`, then the lowest count peeled off). On shape
`0,1,2,3,4,1,2,5` (3.9 s at level 30, TIMEOUT at 900 s at level 60), 82 boxes were tried on 4 cores
(1,754 solver seconds, depth 21) and **none was refuted** (`data/split60_01234125.jsonl`; the run
was stopped). Uniform boxes of the same shape at level 60 with a 100 s limit
(`data/split60_diag.jsonl`): all counts <= 5 TIMEOUT, all >= 6 TIMEOUT, all >= 9 TIMEOUT, all >= 12
UNSAT in 17 s. So the difficulty is not concentrated in a count region that a split could isolate;
only the very-high-count corner is easy. This agrees with track B's finding on its level items
(cube splits do not help; the share cardinality is the hard part). No farm plan for the level-60
share keys is proposed: their cost stays at the estimate above, with single keys beyond one
certificate.

### Share cardinality: encodings, decompositions, symmetry, options (a factor of 2-3, not 10)

Requested follow-up: can a different treatment of the share sum bring the level-60 keys into farm
range (<= 200 G hints for the 132 keys, i.e. at least 10 times cheaper)? CaDiCaL 2.1.3 binary, cold
solves with lazy cycle cuts (`trackA/binsolve.py`); reference shape `0,1,2,3,4,0,1,5` at level 60
(258 s in the production run). Conflicts are the proof-size proxy (`data/enc_expt.jsonl`,
`data/cubes_expt.jsonl`, `data/subwin.jsonl`).

| variant (`trackA/enc2.py`, `expt.py`) | conflicts | seconds (4 jobs at once) |
|---|---|---|
| production counter: one totalizer over the 2,940 `u` literals (37,074 variables, 319,995 clauses) | 1,015,228 | 272 |
| merge tree of the 49 per-corner unary numbers, grouped by centre (19,690 variables, 215,881 clauses) | 1,007,145 | 192 |
| the same as a left-deep chain (sequential counter) | same size; equal on the easy test shape | |
| merge + ordering clauses `u[t+1] → u[t]` (auxiliary symmetry removed) | 942,308 | 170 |
| merge, `--unsat` | 958,652 | 176 |
| merge + order, `--sat` | 1,008,289 | 295 |
| merge + order, `--chrono=0` | 984,963 | 295 |
| merge + order + lex-leader for the transpositions of the 3 unused coordinates | 557,297 | 208 |
| coarser count (only `u[q,t]` with 3 \| t), easy shape `0,1,2,0,3,4,2,5` | TIMEOUT at 120 s (2 s in every other variant) | |
| 7 per-centre cubes "centre c has share <= 8" (cover by pigeonhole) | 2,873,782 in all (205 k - 632 k each) | 505 in all |

- **(b) Counter encodings** change the clause count (1.5 times fewer) and the time per conflict, not
  the number of conflicts. The counter is not where the proof is long.
- **(a) Per-centre distribution.** The pigeonhole cubes triple the total work; they only make the
  largest single proof smaller (632 k conflicts against 942 k). Additivity over sub-windows fails
  outright: the same wall exists on short windows. With 45 s per query, the largest uniform floor
  proved is 0 for 2 centres (`0,1,2`: even "share >= 1" is neither refuted nor satisfied), 4-6 for
  3 centres, 8-11 for 4 centres and 16-24 for the three 5-centre shapes that finished; a 1-centre
  window has a model of share 0. The cost per unit of level is about the same for every window
  length; longer windows only start from a higher free floor.
- **(c) Symmetry.** Lex-leader clauses for the coordinate transpositions that fix the window give
  1.7 times fewer conflicts on a shape with 3 unused coordinates. The hard shapes use 7 or 8
  directions and have 2 or 1 unused coordinates, so at most a factor 2 there, or none. Lean glue it
  would need: the bridge would have to normalise the snake by the stabiliser of the window before
  reading the assignment (a `cubeMap` by the chosen permutation, as `D239Lex` did for the 239
  windows), plus clause soundness for a new clause kind.
- **(d) Options.** `--unsat`, `--sat`, `--chrono=0` are within 7 % of the default in conflicts.
  CaDiCaL has no lookahead cube generator; the count and per-centre cubes above are the
  cube-and-conquer attempts.
- **Best combination** (merge + order + lex-leader + `--unsat`) on two of the shapes that timed out
  at 900 s: `0,1,2,3,4,5,2,4` is now UNSAT in 557 s (2.79 M conflicts; the production encoding again
  TIMEOUT at 900 s), `0,1,2,3,4,1,2,5` still TIMEOUT at 900 s (4.29 M conflicts).

**Verdict:** about 2-3 times in solve time and at most 1.7 times in proof size, where 10 times or
more is needed, and the gain is smallest on the hardest shapes. The 132-key estimate stays far
outside farm range, and every variant other than the production counter would need new clause
soundness in Lean. The measurements point to the model, not the encoding: a low share needs almost
all of the 49 corners to have no empty square, and refuting that is a counting argument that
resolution handles badly. A proof route would need a different certificate kind (counting or
pseudo-Boolean reasoning), which is outside the existing premise kinds.

For comparison, the historical cost per bound: 233: 3.3 G hints; 232: 13.5 G; 231: 41.5 G; 230: about
80 G (in production). 229 by any route measured here is 500 G or more.

## Longer windows

Track B found that the 7-centre witness cycles cannot be extended to 10 directions, so windows of 9
centres are the lever left open by the ceilings. For the count-automaton route this does not help:

- states: 132 shapes × 8^6 = 3.5 × 10^7 at 7 centres (563.6 M edges; the Lean chain is 173 modules,
  2,215 module-seconds, rows of 4 MB). At 8 centres: 505 × 8^7 = 1.06 × 10^9 states; at 9 centres:
  2,332 × 8^8 = 3.9 × 10^10. The 9-centre product does not fit this machine class, and its Lean
  check would be about 1,000 times the K7 chain.
- the 7-centre table is not exhausted: its refinement stalled on a plateau of thousands of
  near-minimal cycles, not on a witnessed ceiling. Longer plain windows only add to a key set that
  already costs 80 G hints at 58,817 windows.
- shape-only automata on 9-centre windows need combined floors that CaDiCaL does not prove in
  20 minutes per item (track B).

## Lean

`lean435/c229/C229Final.lean` (imports `C230Final`; no new generated module):

- `C230.AllShareK K L`: every shape `s` of `L` has `RefutedShare (winOf s) free7 12 K`;
- `C230.window_shareK`, `C230.upper_of_tables_shareK`: the parametrised count above;
- `Snake9.upper_of_refutedK7_share`, `Snake9.upper_229_of_refutedK7` (K = 59),
  `upper_228_of_refutedK7` (K = 90), `upper_227_of_refutedK7` (K = 120), and
  `upper_230_of_refutedK7'` (K = 29 from the 230 premise `AllShareL`, a check of the count).

Built on this machine against the 417-module spec layer of `c230chain.sh` (core stack, ported K7 chain,
`C230*`; mathlib v4.35.0 built locally): `C229Final` compiles in 4 s. `lean435/tools/audit229.py`
(`audit.py final` as `assemble230.py --conditional`: clean directory of public `.olean` files, `--setup`,
strace, no certificate interface) reports, for all seven theorems,
`[propext, Classical.choice, Quot.sound]` and **AUDIT PASSED**
([`audit229/conditional-audit.txt`](audit229/conditional-audit.txt)). No `sorry`, no `native_decide`.

```bash
python3 lean435/tools/prod435.py setup
# mathlib: cp -r /opt/mathlib4-v4.35.0 ~/l435/mathlib4; lake build (roots of milestone 36)
bash lean435/tools/c230chain.sh ~/l435/c230chain
cp lean435/c229/C229Final.lean ~/l435/c230chain/src/
python3 lean435/tools/build.py --src ~/l435/c230chain/src --build ~/l435/c230chain/build C229Final
python3 lean435/tools/audit229.py --spec-src ~/l435/prod/core-src --spec-build ~/l435/prod/core \
  --spec-src ~/l435/c230chain/src --spec-build ~/l435/c230chain/build --work ~/l435/asm229
```

What the theorem is worth: its first premise is exactly the first premise of the 230 theorem, so when
the 230 farm finishes, `AllTab tab230` is discharged for 229 as well, and the whole remaining gap is the
132 share certificates at level 60. Once those exist, the glue is the 230 glue with `G230S` regenerated at
level 59 (`SHARE_CAP` in `lean435/tools/c230.py`, `AllShareK 59` in place of `AllShareL`).

## Files (`trackA/`)

| file | content |
|---|---|
| `bounds.py` | the parametrised count |
| `tier7.py` | corner-share threshold test of a 7-centre window with count bounds (CaDiCaL, lazy cycle cuts) |
| `ladder7.py` | largest level of a ladder proved in a time limit (free or fixed counts) |
| `split7.py` | adaptive count split of one level key (prototype, negative result) |
| `enc2.py`, `binsolve.py`, `expt.py`, `cubes.py`, `subwin.py` | alternative share counters, binary-solver harness, encoding / option / symmetry runs, per-centre cubes, short-window floors |
| `sharemin.py` | CP-SAT search for low-share local models, hinted with track B's witnesses |
| `lpsym.py`, `lpshape.py` | exact minimum cycle mean of the K7 product under symbol-penalty and per-shape weights (run inside a checkout of relaxed-keller's `milestones/10-window-aggregate/scripts`) |
| `data/` | every record quoted above |
