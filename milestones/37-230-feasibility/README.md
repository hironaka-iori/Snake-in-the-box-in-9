# Feasibility of an unconditional m <= 230

Study of 17 November 2026: solver side only, on one 4-core machine. No certificate was replayed and
no Lean module was built. The question was whether an unconditional Lean bound **m <= 230** can be
reached, by which route, and at what cost.

## Answer

1. **The main line (milestones 28-36) cannot realistically reach 230.** Its data type is the k6
   product with counts lumped at 6 (`sym`), plus 5-window, ctx-7 and ctx-8 corner shares.
   - 230 needs `224 P - 129600 Q >= 2^B`, i.e. lambda >= 583.1 (4.859 alpha units) at B = 10.
   - The best solver value is 15268/27 = 565.5 (4.712). The witnessed 5-window ceiling is
     7175/12 = 597.9 (4.983).
   - So the plan would have to prove almost every binding window up to within 0.12 alpha of its
     witnessed SAT value. By the 232 -> 231 step (about 5 times the hints per edge), the
     certificates alone would be of order 150 G hints, for items mostly at levels never measured,
     with a real chance that some needed level is SAT. The plan optimiser was not run for 230:
     with the current records it is infeasible by arithmetic (lambda 565.5 < 583.1).
2. **A different route already has a Lean-checked conditional 230. All of its premises are
   solver-proved, and all its plain windows are DRAT-checked.** On branch
   `claude/relaxed-keller-60ks7i` (milestone 10 of that line, 23 October, Lean 4.19.0, mathlib
   c44e0c8e), `Snake9.upper_230_of_direction_windows_and_sharesK7R34C7W16` compiles with the axioms
   `propext`, `Classical.choice` and `Quot.sound` (`outputs/strengthened-direction-231-reproduction-manifest.json`).
   - **Chain:** a seven-centre count automaton, `K7R34C7W16`. It has 8 directions of memory, 132
     shapes, counts lumped at **8** (`symK 8`: 1..7 and `[8,21]`), 34,603,008 states and
     563,584,123 edges. On alpha alone its mean is **89/19 = 4.684** (minimum cycle mean 75/16),
     with start constant D = -15. That gives `89 m <= 19 Σ α + 678`, which is 231 by itself.
   - **Premise:** none of 58,817 window patterns occurs (2 to 7 centres; 58,640 at radius 3,
     177 at radius 4). Every one of them is drat-trim verified
     (`data/certify_direction_231.log`: 61,104 verified, 0 failed).
   - **Share bonus:** a uniform PARALLEL-square share (weights 6/3/2) of at least 27 on every
     7-centre window. Each of its 132 shape refutations ("share <= 26") is DRAT-checked.
     Combined: `111351 m <= 25718373` (230.97), so **m <= 230**.
   - **Why it beats the main line:** lumping at 6 discards the information that decides the
     binding cycles. With the cap at 7, alpha alone reaches 9/2 on k6 and 89/19 on k7. Our k6 with
     every known key reached 65/16. The 230.1 ceiling of milestone 28 belongs to the cap-6 data
     type only.
3. **The share premise can use the main line's corner share instead, through an existing bridge.**
   The parallel share has no complete Lean bridge (`research/unconditional-231-230` finished one
   six-centre shape of 34). The corner share (`coreShare 12`) does:
   `LocalWindowShareBridge.refuted_share_bridge` accepts any window and any bounds, free counts
   `(1,21)` included. With the K7 walk inequality and `core_charge_sum_le`, a uniform corner share
   of at least **30** on every 7-centre window gives m <= 230 (230.995; 29 gives 231.03).
   **Measured here:** "corner share of the 7 centres <= 29" is UNSAT on 131 of the 132 shapes
   (median 1.3 s, max 267 s). The last shape, `0,1,2,3,4,5,0,1`, timed out at 300 s and is being
   re-run with a 5,400 s limit (see "Status of the open test"). The first shape tested reaches
   >= 60.
4. **Cost of the K7 route:**
   - **Reuse:** 25,189 of the 58,817 windows are implied by keys that are already Lean-certified
     (a contiguous sub-window, in either orientation, of one of the 31,902 plain keys of the 231
     plan, with containing bounds). That leaves **33,628** windows with 5.42 G DRUP lines.
   - **Measured:** 40 LRAT proofs, stratified by DRUP size, with the toolchain of `cert233.core_plain`
     (CaDiCaL `--lrat --no-binary --unsat`, trimmed) give 14.7 trimmed hints per DRUP line. Replay
     is 0.6 of that, as measured in milestone 28, so about 8.8 replay hints per line. The 237 set
     measured 8.4.
   - **Estimate:** about **48 G replay hints** for the uncovered windows: 20,140 under 1 M
     (8.8 G), 13,072 of 1-10 M (31.9 G), 416 of 10-60 M (7.3 G), none above 46 M. The top 1 % hold
     14 %, the top 20 % hold 62 %.
   - **Size data are known for every item.** Each window's DRUP proof already exists, so the
     114x surprises of unmeasured share items cannot happen here. There is also no SAT risk: every
     window is already UNSAT.

## The routes compared

| route | status | new certificates | est. replay hints | main risks |
|---|---|---|---|---|
| main line, k6 cap 6 + 5/ctx shares, lambda >= 583 | solver 565.5; ceiling 597.9 | unknown, >> 231's 20,449 | ~150 G (extrapolated) | levels SAT at the needed value; levels never measured; may be impossible |
| **K7 cap 7, 89/19 + uniform corner share >= 30** | conditional Lean 230 (parallel share) exists; corner floor 131/132 UNSAT | **33,628 windows + 132 share thresholds** | **~48 G** (+ small) | the last floor shape; 4.19 -> 4.35 port of a 563 M-edge chain; bridge glue |
| K7 cap 7 + parallel share >= 27 (as built) | conditional Lean 230 | 33,628 + 132 | ~48 G | parallel-share bridge is new Lean work (one of 34 six-centre shapes done) |
| K6 cap 7, 9/2 (15,959 keys) + uniform corner 6-window share >= 50 | Lean chain exists (232 conditional) | 8,660 windows | ~15 G | the floor: "<= 35" already times out at 240 s on shape `0120310`, so 50 is unlikely to be cheap. Not recommended |

Arithmetic of the corner variant: with `Σ_{j=1}^{m-1} α_j >= (89 m - 678)/19` (the chain), `α_0, α_m >= 4`,
`Σ_k coreShare >= (m-8) X / 7` (every vertex is a centre of at most 7 of the m-8 windows) and
`Σ_{k<=m} (24 α_k + share_k) + 840 (m+1) <= 221136`, m = 231 is impossible as soon as X >= 30.
A higher uniform floor also lowers the lambda that the chain needs, and a lower lambda needs fewer
windows. For 230, X = 40 needs 4.624, X = 50 needs 4.564 and X = 60 needs 4.505 (a smaller minimal
set, which would have to be recomputed). For the same reason, X >= 70 at 89/19 would give 229.

## Lean work for the K7 route

1. **Port** the chain (`WindowAutomatonK7R34C7W16*`, 173 modules, 91 MB of generated source, and
   the generic `WindowAutomaton*` modules: SWAR, transposition, RGS) to Lean 4.35, or regenerate
   it with `gen_lean_swar.py` against 4.35. It checked in 2,215 module-seconds on 4.19. Risk:
   `decide +kernel` on 262,144-bit numbers under the new kernel and elaborator. About 1 session-day.
2. **Window bridge:** derive the premises `hw2..hw7` (`wforbK7R34C7W16 dirs (symK 8 counts) = false`
   for every snake window) from `Refuted (winOf dirs) bounds` certificates. This needs a generated
   cover lemma: every true table entry is backed by a listed key, which is a reused main-line
   certificate or a new one, by bounds monotonicity and sub-window inclusion. The analogues are
   milestone 23's `cover6_rows` and milestone 25's k7 bridge. About 1-2 session-days.
3. **Share wrapper:** a copy of `ShareBonus` with the corner identity (`core_charge_sum_le`,
   `combined_bound` of milestone 28) and 132 `RefutedShare (winOf dirs) [(1,21)]×7 12 29` certificates
   through `refuted_share_bridge`. `countSeq` must be identified with `coreAlpha`
   (`SingletonAlphaBridge`). About 0.5 session-day.
4. **Certificates:** the 33,628 windows through the production pipeline (`prod435.py`,
   `splitfarm435.py`). The CNFs are `wincert.Encoding`, the same encoding as ours: 10 of 10 indexed
   CNFs reproduced their sha256 with this branch's `wincert.py`. The radius is 3 instead of 4, and
   the Lean local model does not depend on the radius. Add the 132 share thresholds, which are
   small: most solve in seconds.
5. **Audit:** the same split audit structure as 231. Expect about 125 GB of new replay `.olean`
   (2.65 B per hint, as measured on 233).

## Cost model (today's numbers)

- **Hints:** about 48 G, with a range of 40-60 G given the replay/est spread of 0.58-0.61 and the
  pooled ratio. L1/L2 families can save up to about 10 % (233 measured 0.888).
- **Kernel time:** 0.3-0.5 ms per hint, so **4,000-6,700 kernel-hours**, plus clause soundness
  (233: 6 % on top).
- **Wall time:** the 231 farm did about 40 G hints in about 1.5 days with about 50 machines. At that
  rate 48 G takes **about 2-2.5 days with 40-50 machines** once the generators are ready.
- **Before the farm:** Lean glue and port, about 3-4 session-days, which can run in parallel with
  the certificate farm (the certificates do not depend on the chain's Lean form). Then the audit.
- **Largest certificate:** about 46 M replay hints, under the 60 M cap. The 416 certificates of
  10-60 M are the split candidates.

## Risks

- **The last share shape.** If `0,1,2,3,4,5,0,1` has a 7-centre corner share of at most 29 (SAT),
  there are two ways out. One is the parallel-share route (premises already DRAT-certified, bridge
  to write). The other is a count-dependent floor for that shape only, which needs a non-uniform
  bonus in the step weight and a regenerated chain.
- **Port risk** of the 563 M-edge SWAR chain to 4.35: memory and kernel behaviour of
  `decide +kernel` on huge numerals. 4.19 needed up to about 2.7 GB per module.
- **Conservative ratios.** Hints per DRUP line vary from 8 to 26 among large proofs, so the 48 G
  could be 40-60 G. No item can turn out SAT.
- **Not re-verified here:** the 89/19 index check and D = -15 (relaxed-keller's `lean_index.py`
  checked the potential on every edge, and the Lean chain re-checks it). The regenerated chain will
  check them again.

## Recommended next step (can start now)

1. **Certificates now.** Feed `data/k7_uncovered.json.gz` (33,628 windows, with case names, intervals,
   radius and DRUP size) to the certificate farm. The items are independent of the Lean glue and
   certain to be UNSAT. Start with the 416 windows above 10 M hints (7.3 G, split route) and the
   13,072 of 1-10 M. Machines: the requested ~40 workers on 15 GB / 4-core boxes are enough
   (largest proof about 46 M hints, about 7 GB RSS at the 233 trend).
2. **Settle the share premise:** finish the last floor shape (running), then generate the 132
   corner share certificates at level 30.
3. **One Lean session:** port and regenerate the K7 chain on 4.35, and write the cover lemma and the
   corner-share wrapper.
4. **Optional and cheap:** raise the uniform floor (X >= 40 is being tested) and recompute the
   minimal set at a lower lambda with costs. This can cut the 48 G, and X >= 70 would aim at 229.

## Status of the open test

See the end of this file (updated when the run finishes).

## Files

| file | content |
|---|---|
| `corner7.py`, `corner7_at.py`, `hard30.py` | uniform corner-share floor of 7- (and 6-) centre windows, counts free (`share7.SubShareEncoding` over all centres, radius 4, M = 12) |
| `lratsample.py` | measured trimmed LRAT hints of a stratified sample of the K7 set |
| `coverage.py` | which windows of a relaxed-keller minimal set our Lean-certified keys already imply |
| `data/k7_shapes_parallel_X26.jsonl`, `data/k6_shapes_parallel_X20.jsonl` | the 132 / 34 shapes, with their parallel-share DRAT records (copied from relaxed-keller) |
| `data/corner7_levels.jsonl`, `data/corner6_levels.jsonl` | floor tests (dirs, T, result, seconds) |
| `data/lratsample_r3.jsonl` | 40 measured proofs |
| `data/k7_uncovered.json.gz`, `data/k6_uncovered.json.gz` | the windows still to certify |
