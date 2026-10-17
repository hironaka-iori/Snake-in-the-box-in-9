# Window exclusions and stronger aggregate bounds

Checkpoint: 17 October 2026.

**Status.** Three new *conditional* upper bounds are proved in Lean: at most **242 edges**, at most **241 edges** with one extra premise, at most **239 edges** from a direction-aware automaton with 145 certified window exclusions, at most **238 edges** with five-centre windows (325 exclusions), and at most **235 edges** with six-centre windows (2,579 exclusions). The premises are exclusions of certain singleton-count patterns on three or four consecutive internal path vertices. Each premise has a **DRAT-checked** unsatisfiability certificate for an explicit local CNF. None is a Lean theorem yet. The unconditional checked interval therefore remains **191 <= a(9) <= 245**.

## What this milestone adds

The incidence identity gives `T + 2*s0 = 9214 - 35*v`. Here `T` is the total singleton-square count, `s0` the number of empty squares, and `v` the number of vertices. The existing proof bounds `T` from below by a potential argument on the count sequence `alpha_0, ..., alpha_{v-1}` along the path. Its worst sequences repeat `2,2,3`, with average `7/3`. Because a universal bound `alpha >= 2` is false, any improvement must restrict *how often* low counts occur.

This milestone asks which count windows a local ball model allows. It then derives the best aggregate inequality those windows support.

1. **Local model** (`scripts/wincert.py`). Fix consecutive path vertices `x_0..x_{k+1}` with internal centers `x_1..x_k` and prescribed counts. The model is the radius-three Hamming ball around the centers. Every clause is a necessary condition on `S ∩ B` for an induced path `S`:
   - the window vertices are selected;
   - every ball vertex has at most two selected neighbours;
   - a vertex whose whole neighbourhood lies in the ball has one or two, and one means endpoint;
   - at most two endpoints occur;
   - each center's count equals its prescribed value: count the absent opposite corners over the 21 coordinate pairs avoiding its path directions;
   - there are no 4-cycles, no 6-cycles inside 3-faces, and no cycle cuts found lazily.

   Up to coordinate relabelling and reversal, there are two 3-center window shapes, with directions `0,1,2,0` and `0,1,2,3`. There are three 4-center shapes: `0,1,2,0,3`, `0,1,2,3,0`, and `0,1,2,3,4`.
2. **Survey** (`scripts/survey.py`, `data/survey_*.json`). Every 3-center count triple with entries 1..6 was decided in both shapes. CaDiCaL with this encoding and an independent CP-SAT model agree on all 432 cases. Of the 216 triples, 144 are feasible in some shape. The minimum mean count over sequences whose consecutive triples are feasible is **14/5**. The worst cycle is `2,3,3,2,4`. The current Lean premises give **7/3**.
3. **Ceiling with four windows** (`data/survey_c4_r3_k5.json`). Every count quadruple in 1..5 was decided in each 4-center shape whose 3-center subwindows are feasible: 654 cases, 293 infeasible. A window `x_0..x_5` with counts `(2,4,2,3)` or `(3,2,4,2)` is infeasible in all three 4-center shapes, and adding only this exclusion raises the minimum mean to **3**. With the complete table the shape-blind minimum mean is still exactly 3, since for example `(3,3,3,3)` is feasible in shape `0,1,2,3,0`. So **241 edges is the limit of shape-blind radius-three windows of length at most four.**
4. **Certificates** (`scripts/certify.py`, `certificates/`, `data/certificates.json`). There are 22 cases:
   - 16 for the triples, in both shapes and both orientations: `(2,2,3)`, `(2,2,4)`, `(2,3,2)`, `(3,2,3)`, and `(4,1,c)` with `4<=c<=6`;
   - 6 for `(2,4,2,3)` and its reversal.

   CaDiCaL produced each DRUP proof. The repository's vendored `drat-trim` verified every one (`work/keep96/vendor/drat-trim`, source hash checked). The gzipped CNF and proof files are about 19 MB.
5. **Positive controls** (`scripts/controls.py`, `data/controls.json`). There are 532 windows: from the 131 bank snakes, the 191-edge witness, and the 137-edge count-one counterexample, including counts 1 and 3. Each satisfies every clause of its CNF with its true counts and selection.
6. **Lean.**
   - `work/spectral/stronger/WindowPotential242.lean` and `WindowPotential241.lean` use core Lean only. They prove the sequence inequalities `14*n <= 5*sum + 12` and `3*n <= sum + 4` by potentials checked by kernel evaluation of finite tables.
   - `AggregateWindowConditional.lean` uses mathlib and combines them with the existing incidence identity. It proves `upper_242_of_certified_windows` and `upper_241_of_certified_windows` for the original `Snake9.Snake`.
   - The (2,2,2) case is discharged by the existing theorem, and the count-one neighbour bound and endpoint bound are reused. Only the listed window premises remain as hypotheses.
   - *Reproduction:* a fresh source-only run of `verify_strengthened.py` succeeded. It covered 156 steps: core, incidence theorem, every strengthening module including these three, and the final audit. Both conditional theorems, and the unconditional 245 interval, audit to `propext`, `Classical.choice`, and `Quot.sound` only. The manifest and combined log are `outputs/strengthened-window-reproduction-manifest.json` and `outputs/strengthened-window-reproduction.log`. The run used `--core-targets Snake9 PathStructure CubeLocal SquareCounterexample SingletonSquareLemma OptimalityTarget`, the only core modules the chain imports.

7. **Independent judge** (`scripts/judge.py`, `data/judge.json`). This is a high-level decision procedure that reuses none of the generating code. Its verdict is **ACCEPT**:
   - (A) It re-encodes every premise from the definitions, with a different variable order and a different cardinality encoding. It checks the recorded cycle cuts are genuine cycles, refutes each formula with Glucose, and verifies each proof with `drat-trim`. All 22 are verified.
   - (B) It classifies every vertex-only clause of the stored certificates semantically as a window unit, a degree-3 star, an interior-neighbour clause, a 4- or 6-cycle of a face, or a cycle cut. None is unclassified.
   - (C) It normalises 4,979 windows of real snakes, every window with a count at most 4 plus a sample. Each satisfies the judge's encoding with its true counts.
   - (D) An independent dynamic program reproduces 245 for the proved premises and 244 for the existing (2,2,3) condition, and gives 242 and 241 for the new premise sets.

   This gives two independent implementations of the encoding, but it is still a test of the bridge, not a proof.

| Assumed window exclusions | Minimum mean | Bound |
|---|---|---|
| proved Lean premises only | 7/3 | 245 edges (unconditional) |
| + (2,2,3) | 5/2 | 244 (existing conditional theorem) |
| + (2,2,4), (2,3,2), (3,2,3), (4,1,4..6) | 14/5 | **242** (new conditional theorem) |
| + (2,4,2,3) | 3 | **241** (new conditional theorem) |

The constants follow from `5*T >= 14*(v-2) - 12 + 40` and `T >= 3*(v-2) - 4 + 8` respectively. Exact dynamic programming over count sequences, in `scripts/aggregate.py`, confirms that the patterns admit 243 and 242 vertices. They exclude one more vertex in each case.


## Direction-aware automaton: conditional bound 239

The shape-blind ceiling above is 3 (241 edges). Tracking which coordinates the path uses breaks it, because the only low-count windows that survive at radius three are tied to particular transition shapes, and consecutive windows of those shapes cannot be chained for long.

**Abstraction** (`scripts/refine.py`). A state is the canonical shape of the last six transition directions, up to relabelling (12 induced shapes), together with the last three lumped counts (`min(alpha,6)`, 216 combinations): 2592 states. A transition appends one direction label and one count. It is allowed unless the seven-direction block is not an induced path or some window of two, three or four consecutive centres ending at the new vertex is known to be infeasible in the radius-three local model. Unknown windows are allowed, so the automaton over-approximates real snakes and its minimum cycle mean is a valid lower bound on the average internal count given the exclusions it uses.

**Refinement.** Howard's policy iteration finds a minimum-mean cycle; the windows on it are sent to the SAT oracle; infeasible ones are added. With six directions of memory the mean rises from 8/3 to **10/3** in five rounds (four or five directions stall at 3; seven add nothing). With five-centre windows and seven directions it reaches **7/2**.

**Minimal exclusions** (`scripts/minimize.py`). Of 333 relevant infeasible windows, dual slack pruning keeps the mean 10/3 and the integer potential (range 8) with **145**; an exact-greedy pass over the vertex bound reaches 93 (mean 23/7, same bound by dynamic programming). The potential route uses the 145 set:

| route | exclusions | mean | potential range | edge bound |
|---|---|---|---|---|
| L=6, k=4 (potential, Lean) | 145 | 10/3 | 8 | **239** |
| L=6, k=4 (exact DP) | 93 | 23/7 | — | 239 |
| L=7, k=5 (potential, Lean) | 325 | 7/2 | 6 | **238** |
| L=7, k=6 (potential, Lean) | 2579 | 4 | 6 | **235** |

Arithmetic for 239: the potential gives `3 Σ_{j=6}^{m-1} min(alpha_j,6) ≥ 10 (m-6) - 8`; with `alpha_1..alpha_5 ≥ 1` and endpoints at least four, `3 T ≥ 10 m - 36`; with `T ≤ 9214 - 35 (m+1)` this is `115 m ≤ 27573`, so `m ≤ 239`.

**Certificates** (`scripts/certify_direction.py`, `data/direction_certificates.json`, `certificates/direction/*.cnf.gz`). Every one of the 145 windows has a drat-trim-verified refutation. The CNF files are committed; the DRUP proofs (250 MB) are not, their SHA256 is recorded and the script regenerates them. `scripts/judge.py --index` re-encodes all 145 independently and refutes them with Glucose: 145 verified (one case needed a solo rerun because the batch hit the checker's time limit under CPU contention; `data/judge_direction.json`). `scripts/direction_bound.py` rebuilds the automaton from the certificate index alone, checks the integer potential on every one of the 29,559 allowed edges and recomputes the exact bound (`data/direction_bound_L6_k4.json`). The 325-window set for 7/2 is certified the same way (`data/direction_certificates_k5.json`, all 325 verified; `data/direction_bound_L7_k5.json` re-checks its potential and bound; the independent judge re-encodes and refutes all 325, `data/judge_direction_k5.json`). Certifying it became practical only after the lazy cycle-cut loop was made incremental (one CaDiCaL instance per window instead of a cold restart per cut): the remaining 219 windows then took minutes instead of hours.

**Lean.** Six modules in `work/spectral/stronger/`:

- `WindowAutomatonDefs.lean` (core Lean): first-occurrence relabelling `canon`, restricted growth strings, the parity test `inducedPattern` (a block of directions must not have all multiplicities even, nor exactly one odd when it has two or more steps), enumeration helpers.
- `WindowAutomatonData.lean` (generated by `scripts/gen_lean_automaton.py`): the exclusion table and the potential as bitmask literals, the step test `check`, and `step_table : allRGS 7 0 check = true`, which the kernel evaluates in about a minute (877 restricted growth strings times 1296 count combinations). The generator re-implements `check` in Python and asserts it on the same 29,559 transitions before writing the file.
- `WindowAutomatonLemmas.lean` (core): `canon` is invariant under injective relabelling, as is `inducedPattern`; so the table applies to an arbitrary seven-direction window (`step_raw`).
- `WindowAutomatonSequence.lean` (core): the telescoped inequality `total_bound : 10 m ≤ 3 Σ_{j=1}^{m-1} alpha_j + 60`.
- `WindowAutomatonBridge.lean` (core, imports the standard-library core): `pathDir` extracts the flipped coordinate of each edge; the XOR of a block of unit vectors has bit `b` equal to the parity of the count of `b`, so `distinct` and `induced` of `Snake9.Snake` give `inducedPattern` for every window.
- `AggregateDirectionConditional.lean` (mathlib): `upper_239_of_direction_windows`. Its only premise is that no two-, three- or four-centre window of the snake has a direction shape and lumped counts listed in `forbMask`; everything else is proved.

The five-centre automaton (34 shapes, 44,064 states) is handled the same way by `WindowAutomaton5Data/Table/Sequence.lean` and `AggregateDirection238Conditional.lean` (`upper_238_of_direction_windows5`). Its step table is too large for one kernel evaluation (a single file was killed after 12 minutes), so `scripts/gen_lean_automaton5.py` emits one module per canonical 7-shape, `WindowAutomaton5Shard0..33.lean`, each enumerating the next label and all 6^5 symbol combinations in about a minute, and a kernel-checked membership lemma shows every induced restricted growth string of length eight is a listed shape followed by a label below nine (`check5_of_rgs`). Arithmetic: `2 Σ_{j=7}^{m-1} min(alpha_j,6) ≥ 7 (m-7) - 6`, so `2 T ≥ 7 m - 21 - 6` and `77 m ≤ 18385`, giving `m ≤ 238`.

All of these audit to `propext`, `Classical.choice`, `Quot.sound`. They are included in `verify_strengthened.py`; a fresh 200-step source-only run (core, incidence, every strengthening module including the 34 shards, final audit) is recorded in `outputs/strengthened-direction-reproduction-manifest.json` and `outputs/strengthened-direction-reproduction.log`.

Reproduce:

```sh
cd milestones/10-window-aggregate/scripts
python refine.py --L 6 --k 4 --K 5 --radius 3          # refinement; writes data/refine_L6_k4_K5_r3.json
python minimize.py --L 6 --k 4 --K 5 --target-edges 239
python certify_direction.py --set ../data/minimal_L6_k4_K5.pass1.json
python direction_bound.py --index ../data/direction_certificates.json --L 6 --k 4 --K 5
python judge.py --index ../data/direction_certificates.json
python gen_lean_automaton.py --index ../data/direction_certificates.json
```

The first command needs the survey files as a seed and about ten minutes; the rest take a few minutes each.

**Still not established.** The geometric bridge from a snake window to the local CNF, and a kernel-checked replay of the refutations, are the same gaps as for 242 and 241; the direction-aware premise has 145 windows instead of 22. Beyond 238: `scripts/refine_fast.py` is a vectorised rewrite of the refinement loop (allowed-transition masks per shape pair from per-window-shape tables, `reduceat` Bellman-Ford and dynamic programme) that handles 10^5-10^6 states; `scripts/minimize_fast.py` is the matching minimiser (blocker counts per extension); `scripts/gen_lean_automaton_k.py` generates the whole Lean chain for any (L, k, lambda) with sharded kernel checks. Radius four with four-centre windows converges to the same 10/3 as radius three (`data/refine_L6_k4_K5_r4.json`, the cycle (2,2,6) survives), so radius alone does not help at k = 4. Six-centre windows at radius three are cheap (ball of 316 vertices, about 0.1 s per query, real-snake controls pass), which makes the next step affordable.

## Six-centre windows: conditional bound 235

With seven directions of memory and windows of up to six centres (34 shapes × 6^5 counts = 264,384 states, up to 2.7 million allowed transitions) the refinement loop reaches mean **4** after 186 rounds (`data/refine_L7_k6_K5_r3.json`). Batching the windows of every near-minimal cycle of Howard's policy graph, not only the minimum one, is what made the later rounds productive. The vectorised minimiser keeps **2,579** windows (3 two-, 64 three-, 298 four-, 2,030 five- and 184 six-centre), with an integer potential of range 6 (`data/minimal_L7_k6_K5_r3_cheap.json`). Four high-count four-centre windows of the first minimal set (`data/avoid_k6.json`) had refutations that did not finish in hours; the loop was rerun with those treated as feasible and a 60-second limit per oracle query, and reached mean 4 again with cheap substitutes, so every window in the final set certifies in at most a minute. Arithmetic: `Σ_{j=7}^{m-1} min(alpha_j,6) ≥ 4 (m-7) - 6`, so `T ≥ 4 m - 26` and `39 m ≤ 9199`, giving `m ≤ 235`; the exact dynamic programme gives the same 235. The kernel check needed a rewrite of the enumeration (`work/spectral/stronger/WindowAutomatonLoop.lean`). Measurements on one (shape, label) pair of 46,656 transitions: the original closure-nested loop over symbols took 400 s and 7 GB; a flat 46,656-deep structural recursion overflows the kernel stack; `decide` on a `Nat` inequality costs about 0.3 ms per use and every bit test on a table of 46,656 bits allocates the whole shifted table, because the kernel substitutes expressions and does not share the value of a closed subterm across loop iterations. The working design is a `Nat.rec` loop that tests the body before the recursive call (`allBelowR`, constant stack), tables indexed by the base-6 symbol code, an outer loop over the four oldest symbols and an inner loop over the two newest, and `letN (v + 1) k = k v`, whose major premise forces the kernel to normalise the 36-bit window of each table once per outer step and re-enter it as a numeral; the inner loop then uses only `Nat.beq`, `Nat.ble`, `>>>` and `&&&` on small numerals. One pair now takes 5 s and 0.6 GB, a shard of nine pairs 35-50 s, the 34 shards about ten minutes on three cores. The transport lemmas (`bitT_win`, `fldT_win`) relate windowed bits and 4-bit fields to the original tables through `Nat.testBit`, and a generic extraction lemma proved on abstract tables (`checkT_spec`) keeps every elaborator-side unification away from the concrete loop (a `simp` under the loop binder on the concrete tables made the kernel unroll all 46,656 iterations).

All 2,579 windows are drat-trim-certified (`data/direction_certificates_k6.json`); `refine_fast.py --index` rebuilds the automaton from the index alone and re-checks the potential on every allowed edge (`data/direction_bound_L7_k6.json`); the independent judge re-encodes and refutes them (`data/judge_direction_k6.json`). The Lean chain is produced by `scripts/gen_lean_automaton_k.py` (modules `WindowAutomatonK6R3*`, 34 shards, and `AggregateDirectionK6R3Conditional.lean` with `upper_235_of_direction_windowsK6R3`); the generated potential is defined as `min 6 field`, so its range bound is definitional and the Lean constant matches the dynamic programme. Radius four with four-centre windows gave no gain (10/3, `data/refine_L6_k4_K5_r4.json`).

## Ceilings of count-only window methods

Explicit adversaries (found by the collaborating local session and re-checked here with `scripts/wincert.py`) bound what any automaton over lumped singleton counts can prove:

- `Q9 = Q5 × Q4` with two disjoint induced 14-cycles in `Q5` placed on even and odd fibres gives an induced 2-regular set of 224 vertices with counts 2 (×64), 5 (×128), 7 (×32); all its 2-, 3- and 4-centre windows are feasible at radius three, so no radius-three automaton with at most four centres can exceed mean 30/7 (about 233 edges). One 5-centre window at radius three refutes it.
- `Q9 = Q6 × Q3` with two disjoint induced 26-cycles in `Q6` gives 208 vertices with lumped mean 69/13; all windows with at most five centres are feasible at radius three and all with at most four centres at radius four, so those routes stop near 227 edges. Six-centre windows at radius three are the first lever that can see it.
- Real 191-edge snakes have lumped mean `min(alpha,6)` about 5.92 and true mean `alpha` about 8.7, so a lumped-at-six method cannot pass about 224 edges at any radius and any count-only method cannot pass about 209.
- Charging each empty square `2/21` to each selected vertex adjacent to it (a square has 28 neighbours forming seven disjoint squares, each holding at most three selected vertices) is computable from the radius-three ball (`Encoding(..., empties=...)`), but the count pattern alone forces almost nothing about it there: `e(mid) <= 4` stays feasible for patterns such as (2,5,7) or (5,5,5), because selected vertices at distance two and three (free at the boundary of the ball) kill the adjacent squares. With that charging the adversaries sit at 225.7 and 212.0 edges and real snakes at 199, so the lever only pays as a joint `(alpha, e)` state at radius four.

The six-centre refinement terminated with a locally feasible cycle of mean 4 containing six lumped-six counts, so the cheapest next lever is a finer lump cap at five or six centres (`refine_fast.py --K 7`, symbols 1..7 and `>= 8`; cached range answers imply the finer exclusions).

## What is not established

- **The geometric bridge.** A snake with such a window can be normalized so that the window has a canonical shape, by a translation and a coordinate permutation. Its intersection with the ball then satisfies every clause. That argument is short and standard, but it is not formalized here. The same gap exists for the earlier radius-three (2,2,3) certificates in `milestones/07-window-223/`.
- **DRAT is not Lean.** `drat-trim` is an independent, widely used checker, but it is not part of the Lean kernel. The CNF generator is also unverified, though the positive controls exercise it. Converting these certificates into Lean, as was attempted for (2,2,3), remains open.
- **Beyond 241.** The shape-blind four-window ceiling is 3, so further progress here needs more information:
  - *Direction-aware states.* Feasible low quadruples such as `(3,3,3,3)` occur only in shape `0,1,2,3,0`. Three consecutive windows of that shape would make `x_7` adjacent to `x_0`, so an automaton that also tracks directions should exceed mean 3. `scripts/direction_automaton.py` does this: it tracks the last seven directions and checks each window against the survey for its own shape. Its minimum mean is about **10/3**, found by binary search. With small constants that would give roughly 239–240 edges. It relies on many more solver-only exclusions, none certified yet.
  - *Radius four.*
  - *The empty-square term `s0`, which every current bound discards.* A CP-SAT probe at radius four found that a count-one vertex forces at least four empty squares meeting its neighbours. At radius three nothing is forced. This is uncertified.

## Reproduction

From the repository root, with `python-sat` installed:

```sh
cd milestones/10-window-aggregate/scripts
python survey.py --centers 3 --radius 3 --kmax 6 --out ../data/survey_c3_r3.json
python survey.py --centers 4 --radius 3 --quads quads.json --out ../data/survey_c4_r3_k5.json   # quads.json: the alpha lists in survey_c4_r3_k5.json
python aggregate.py --survey ../data/survey_c3_r3.json
python certify.py
python controls.py
python judge.py                 # independent end-to-end verdict
python direction_automaton.py   # exploratory, about 10/3
```

`wincert.ensure_drat` compiles the vendored `drat-trim` into the ignored `.build/` directory after checking its source hash. For the Lean modules, run `python work/spectral/verify_strengthened.py --mathlib-dir /path/to/mathlib`. It now includes the three new modules and audits both conditional theorems.
