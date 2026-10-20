# Collaborator handoff

Checkpoint: 19 October 2026. Manuscript authors: Iori Hironaka, Tommy Ma, and Steven Zhan.

## Current assignment: constructive search

This investigation now concentrates on a 196-edge construction; collaborators
continue the upper-bound work. The [new construction milestone](milestones/12-construction-196/README.md)
records a Lean-checked zero-defect criterion, approximately 31 million pilot
proposals, and exact fragment-repair experiments. No valid improvement over
191 edges was found. The two best 196-edge walks have seven chords each.
That initial experiment is now followed by the
[population and adaptive-repair comparison](milestones/13-diverse-construction/README.md).
The added 440 million proposals found no valid improvement; the best saved
walks have six chords. Retaining multiple candidates showed no consistent
benefit at the longer budget. Every saved best walk from those four long runs
has a known bank prefix and all defects touching its five appended vertices.
Four solver-guided interior repairs ended unresolved. The next constructive
direction relaxes connectivity, allowing a path and cyclic components, then
excludes those cycles using the existing checked cycle-exclusion lemma.
This is now implemented in [milestone 14](milestones/14-component-construction/README.md).
A concrete 197-vertex seed consists of one 14-edge path and seven 26-cycles;
its vertex count, degrees, partition, and cycle-cut validity passed Lean.
Sequential cycle cuts produced a 40-edge path and six 26-cycles on the same
number of vertices. The next round was unresolved. Continue from the saved
seven-component state with both accumulated cuts retained. It remains a
disconnected intermediate configuration, not an improved snake witness.

Further targeted mergers are recorded in [milestone 15](milestones/15-component-mergers/README.md).
The fixed 40-edge path is locally blocked, while unrestricted replacements of
the path and one or two cycles remained unresolved. The signed frozen-cycle
constraint has a Lean proof. [Milestone 16](milestones/16-cycle-reservoirs/README.md)
supplies two checked disjoint 14-cycles in Q5, a 224-vertex product, and additional
197-vertex disconnected states. The next constructive task is to use its two
4,973-row local-state tables in a global cell model. Four shared connector
vertices govern cross-cell edges; a checked local cost lemma explains why a
connector with four internal neighbors must omit at least three when it uses
an external edge. Costs can overlap and do not give a global bound.

Synchronization incorporated the completed KEEP=112 aggregate receipt covering
all 262 oriented bank entries, the bounded KEEP=96 survey, and conditional
window bounds through 238. The unconditional 241 theorem is now part of this
branch and was audited on macOS and again from a fresh Linux environment. The
bounds 238 and, with radius-four windows, 237 are now also unconditional Lean
theorems, audited on Linux (see the window-exclusion section below). Historical priorities below describe previous checkpoints; they do not assign
new upper-bound work to this constructive investigation.

## Where the investigation stands

The exact optimum is unresolved; no candidate value receives privileged status. The earlier conjecture **a(9) = 196** has low confidence. For n = 3,...,8, subtracting 3*2^(n-3) from the known maxima leaves 1,1,1,2,2,2. Continuing the correction in doubling blocks of three predicts 196. An equally exact additive-block fit predicts 195. The first eight values therefore do not determine the ninth, and interpolation supplies no geometric proof.

The fully Lean-checked global interval is now **191 <= a(9) <= 237** (see the window-exclusion section below). The 245 argument: the strengthened square-face bound combines the incidence identity with endpoint singleton counts at least four, count-one neighbors at least four, and exclusion of three consecutive internal count-two vertices. The earlier arguments still supply the weaker bounds 238, 241, 242, 247, 248, 251, 254, and 255. No 192-edge improvement, 196-edge construction, exclusion of 197 edges, or exact optimality result has been obtained.

The strongest completed global upper bound is 237 (window-exclusion section below; `outputs/upper-bound-237-audit-linux.log`). For the 245 step, normalization from arbitrary path indices, both five-vertex window shapes, all outer missing-family cases, the final shared-coordinate classification, and the aggregate potential estimate are checked in Lean. An independent final import audit passed. All theorem audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The fresh source-only reproduction succeeded for all151 steps, including the148 strengthening modules, with every source hash rechecked. Saved manifests and logs are in `outputs/strengthened-reproduction-*` and the versioned `outputs/strengthened-245-reproduction-*` files. The exact optimum remains open.

The earlier universal two-singleton-square claim for internal vertices is false. A checked 137-edge counterexample has zero at path index 127, endpoints 145 and 288, and exactly one singleton square, {0,4,8,12}. Its distance along the path from the nearer endpoint is ten. Thus simply excluding the first few vertices near the endpoints does not repair that universal assertion. This example does not exclude a stronger statement restricted to longest paths.

## Window-certificate checkpoint, 16 October 2026

The repeated-coordinate radius-three (2,2,3) Boolean certificate passed all 61 Lean modules and its final axiom audit. The distinct-coordinate certificate is still being checked. The completed counter proof connects actual singleton counts to the ordered lists of 21 eligible corners and supplies the full auxiliary threshold assignment. Endpoint rules and all 112 retained cycle cuts are also checked. Exact assembly of all Boolean input clauses and arbitrary-window coordinate normalization remain open, so the global interval is unchanged.

See [milestone 07](milestones/07-window-223/README.md) for the source hashes, reproduction commands, and remaining obligations. The collaborator branch review is recorded [separately](milestones/08-exhaustive-search/upstream-review-2026-10-16.md); its restricted DFS results do not settle the global optimum.

## Completed milestone: incidence proof

The formerly pending upper-bound verification is complete. `work/spectral/SquareIncidence.lean` proves the following quantities directly from the cube and path definitions:

- E: total number of empty squares counted from each possible corner.
- T: total singleton incidences, counted at their selected vertex.
- W: total selected centers with both neighbors in a distinct coordinate pair selected.

For a path on v vertices, the checked identity is

`2*E + 4*T + 144*v = 36864 + 4*W`.

The checked estimates T >= v and W <= v-2 (for v >= 2) give v <= 255, hence at most 254 edges. The proof handles all path lengths. It uses the same snake definition as the 191-edge witness and assumes no census equation.

This replaces the need to certify all original canonical-square bijections before establishing 254. The old conditional arithmetic module remains as a record of the first approach. The exact canonical census equalities have not separately been certified; they are unnecessary for the new theorem. The paper now presents the checked proof.

Reproduce with `python work/spectral/verify_incidence.py --mathlib-dir /path/to/mathlib --fresh-core` after preparing the pinned dependency.

## Completed milestone: adjacent singleton exclusion and bound 251

Write alpha(x) for the number of singleton coordinate squares at a selected vertex x. The new theorem states that two adjacent internal path vertices cannot both have alpha = 1. At a normalized internal vertex with selected unit neighbors a,b, a unique missing pair c,d forces every other eligible pair vertex to be selected. The continuation through a must use c or d; otherwise three distinct selected vertices would have degree at most one. Applying this geometry at the adjacent vertex yields either three disjoint groups each requiring an endpoint, or a selected eight-cycle. Both are impossible in an induced path.

Together with alpha >= 1, this gives alpha(x)+alpha(y) >= 3 for consecutive internal vertices. The checked finite-sum argument handles both endpoints and all short paths, and gives 3*m <= 2*T for a path with m edges. Substitution in the same incidence identity proves m <= 251. No solver exclusion is used in this proof.

The maintained proof sources are `work/spectral/stronger/`. Reproduce the full strengthened proof with `python work/spectral/verify_strengthened.py --mathlib-dir /path/to/mathlib`. This driver always builds a fresh source-only core, then the incidence theorem and all strengthening modules, and audits the final interval and general prefix theorem. Per-step logs and a SHA256 manifest are retained in its ignored build directory. The research directories retain explicitly frozen development snapshots, not alternative maintained proof projects.

## Completed milestone: adjacent counts (1,2) and bound 248

The next local theorem excludes adjacent internal singleton counts (1,2). After translating the count-one vertex to zero, its unique missing pair forces the root geometry as above. At its count-two neighbor, exactly two missing coordinate pairs remain. The proof treats all possibilities for their incidence with the other root arm: neither missing pair contains it, a missing pair uses the root's exceptional coordinate, two pairs use the arm, or one does and the other does not. Every branch forces more than two distinct path endpoints or a selected cycle. The finite-set classification and geometric contradictions are checked in Lean without solver premises.

Consequently every consecutive internal pair has singleton-count sum at least four. Including both endpoints gives `4*m <= 2*T+2`; the same incidence identity then proves `m <= 248`. `UpperBound248.lean` combines this unconditional upper bound with the existing 191-edge witness. The reproduction command above now checks both strengthenings and the final 191--248 interval.

## Completed milestone: endpoint count four and bound 247

At an endpoint, translate its sole selected neighbor to unit coordinate a. Singleton squares correspond to missing pairs among the other eight coordinates. Three or fewer missing pairs leave either at least three isolated coordinates, or exactly two isolated coordinates and three disjoint missing edges. The first case creates three endpoint demands. The second forces selected triples that prevent the neighbor a from continuing, again creating too many endpoints. The normalization, finite-family classification, and geometric contradictions are all checked in Lean.

Combining endpoint counts at least four with the internal pair sum at least four gives `4*m+10 <= 2*T`. The incidence identity proves `m <= 247`. A separate checked 120-edge path attains exactly four singleton squares at its first endpoint, so that local estimate is sharp. The reproduction driver checks the unconditional `verified_interval_191_247` and all preceding strengthening theorems.

## Completed local strengthening: adjacent counts (1,3)

`AdjacentOneThreeExclusion.lean` unconditionally excludes adjacent internal counts (1,3), so an internal neighbor of an internal count-one vertex has count at least four. A symbolic finite-set argument with three missing pairs produces either three disjoint endpoint groups, or two such groups and an additional group from isolated coordinates. Every step and arbitrary-index normalization is compiled with the standard foundations only. This milestone had41 maintained modules. The local theorem alone did not improve247, because an all-two internal count sequence still satisfied those adjacent restrictions.

## Completed milestone: no three consecutive twos and bound 245

`UpperBound245.lean` proves that three consecutive internal vertices cannot all have singleton count two, and derives the unconditional interval191--245. The proof first normalizes the five-vertex window into repeated- or distinct-coordinate shapes. The latter's outer missing families reduce through exceptional, common-hole, star, mixed, equal-pair, and disjoint-pair cases to ordinary pairs sharing one coordinate. A kernel-checked finite classification reduces this last case to20 labelled middle families, all excluded by explicit endpoint, degree, or cycle arguments. Every coordinate reduction is proved; no solver result or incomplete bank census is assumed.

For v selected vertices and total singleton count T, a finite potential yields `3*T >= 7*v+5`. The incidence identity and `W <= v-2` give `T+35*v <= 9214`, hence `112*v <= 27637`. Therefore v<=246 and the edge count is at most245. The final theorem uses the original `Snake9.Snake` and the original checked191-edge witness. The project now has148 maintained strengthening modules.

The next priorities concern improving beyond245 and finding a longer verified construction. Probes excluding adjacent counts (1,4) and two internal count-one vertices at path distance two remain uncertified observations. A checked (2,2) example prevents assuming every adjacent pair has sum at least five. The repeating count pattern (2,2,3) still meets the established local count restrictions and is a bottleneck for improving their aggregate consequence.

## Latest aggregate work: window exclusions (17-19 October 2026)

`milestones/10-window-aggregate/` addresses "Priority 2" below. Because `alpha >= 2` fails universally, it bounds how often low counts can occur, via local window exclusions rather than a pointwise bound.

- The radius-three local model allows only 144 of the 216 count triples in 1..6. The resulting aggregate ceiling is mean 14/5, versus 7/3 from the proved premises.
- With (2,2,3), (2,2,4), (2,3,2), (3,2,3), and (4,1,4..6) excluded, the Lean theorem `upper_242_of_certified_windows` gives 242 edges. A fresh 156-step source-only reproduction, in `outputs/strengthened-window-reproduction-*`, also re-proved 245.
- Also excluding (2,4,2,3), the theorem `upper_241_of_certified_windows` gives 241 edges.
- **These 22 exclusions are now Lean theorems, so 242 and 241 are unconditional** (`UpperBound241.lean`: `upper_bound_242`, `upper_bound_241`, `verified_interval_191_241`, axioms `propext`, `Classical.choice`, `Quot.sound` only). `LocalWindowBridge.lean` moves each snake window to canonical position and proves the abstract axioms of `LocalWindowModel.lean` there; `LocalWindowSat/` proves that every clause of each UNSAT core follows from those axioms; and `LocalWindowUnsat/` replays the drat-trim LRAT refutation of each core, segment by segment with `decide +kernel`, through the checker `LratCheck.lean`, whose soundness is proved in Lean. Audited on macOS (`outputs/upper-bound-241-audit.log`) and from a fresh Linux environment (`outputs/upper-bound-241-audit-linux.log`).
- All 22 premise cases have `drat-trim`-verified refutations of explicit CNFs, and 532 real-snake windows pass as positive controls.

- A direction-aware automaton (last six transition directions up to relabelling, last three counts; 2592 states) refined against the SAT oracle reaches mean 10/3 with 145 certified windows. `upper_239_of_direction_windows` gives **239 edges**; the potential table is kernel-checked and the parity bridge from `Snake9.Snake` is proved. With five-centre windows the same loop reaches 7/2 with 325 certified windows; pruning keeps 175 of them with the same mean (potential range 10), and `upper_238_of_direction_windows5` gives **238 edges** (44,064 states, checked in 34 shards).
- **The 175 exclusions are now Lean theorems, so 238 is unconditional** (`UpperBound238.lean`: `upper_bound_238`, `verified_interval_191_238`, axioms `propext`, `Classical.choice`, `Quot.sound` only; `outputs/upper-bound-238-audit-linux.log`, Lean 4.19.0, mathlib c44e0c8e). The bridge is `DirectionWindowBridge5` with `AggregateDirection238Unconditional.upper_238_of_refuted`; clause soundness is `LocalWindowDirSat5` (175 Sat modules); the kernel replays of the 175 LRAT refutations built completely (14,206/14,206 modules, 0 failed; 2,803 check modules, 39.5 kernel-hours, at most 3.93 GB each; 11,038 data modules, 13.5 h; `LocalWindowDirUnsat5` in 230 s at 7.63 GB; `outputs/upper-bound-238-replay-linux.log`). The chain modules were reused from the compile in `outputs/aggregate-238-chain-175-linux.log` (47 min); `UpperBound238` itself took 163 s and 9.7 GB. The audit was made on Linux only against the incrementally built core; the fresh source-only path `work/spectral/verify_strengthened.py --with-238` has not been run yet.
- 239 stays a conditional theorem: it is subsumed by 238, so the replay of its 145 refutations was stopped unfinished and no `UpperBound239` build exists.
- **Radius-four windows give 237, now unconditional** (`UpperBound237.lean`: `upper_bound_237`, `verified_interval_191_237`, axioms `propext`, `Classical.choice`, `Quot.sound` only; `outputs/upper-bound-237-audit-linux.log`). The local model does not depend on the ball radius, so the same bridge applies. The refinement loop at radius four reaches mean 42/11; `prune_costly.py --target-edges 237` keeps 387 of the 1351 windows of the minimal set (mean 51/14, 6-bit potential of range 61), all DRAT-certified (`data/direction_certificates_r4b.json`). Cores were extracted by a CaDiCaL portfolio (289 M LRAT hints in total); clause soundness is `LocalWindowDirSatR4b` (packed data); the replays use `LratFast2` (cached start database) with `LratFast2F` (`check2f`) on segments of more than 2000 lemmas and were compiled with `lean` directly (`--direct`): 3,287 check modules, 34.0 kernel-hours, about 12 h (three runs) wall time (`outputs/upper-bound-237-replay-linux.log`). The chain `WindowAutomaton5R4b*`, `DirectionWindowBridge5R4b`, `AggregateDirection237*`, `UpperBound237` compiles with standard axioms (`outputs/aggregate-237-conditional-chain-linux.log`). Audited on Linux only against the incrementally built core; no fresh source-only reproduction yet.
- The 236 set (732 radius-four windows, 371 shared with 237, all DRAT-certified; mean 42/11, potential range 48) has its conditional chain compiled with standard axioms (`outputs/aggregate-236-conditional-chain-linux.log`) and its cores and clause-soundness modules built; the replays of the 361 new windows (644 M hints) are being generated and built. 236 is not yet a theorem.

Remaining upper-bound work: 237 is done; the 236 replays are in progress. After that, the empty-square term `s0` is the main lever (a target near 231). Local window methods of this kind are capped near 227 edges (`milestones/11-local-ceiling/`), so reaching 196 needs global arguments.

For the 241 step, untested four-vertex windows were counted as feasible, radius four was not used, and the empty-square term `s0` was discarded; the direction-aware windows behind 238 showed that 241 was not the limit of this method. The term `s0` is still discarded.

## Priority 1: find a longer construction outside the exhausted families

A verified 192-edge example would immediately disprove the candidate optimum 191. A 196-edge example would establish the conjectured lower bound, but still would not prove optimality.

The current evidence favors widening structural diversity over repeating small changes to the same seeds:

- Every 152-vertex prefix obtained from either orientation of the 131 supplied 191-edge snakes was exhausted without reaching 193 vertices. With only 144 vertices retained, 53 searches remained unresolved at the node limit.
- Every two-vertex-deletion neighborhood of the 131 examples was excluded for a 192-edge target by the solver. Larger neighborhoods remain largely unresolved.
- The supplied 98-edge Q8 seed has no 97-edge partner under the tested exact one-crossing joining model, at either endpoint. Isometric placements of the tested truncated copy also fail. This does not classify all optimal Q8 seeds.

Useful constructive directions are structurally different Q8 seeds, constructions with multiple crossings between layers, and larger changes that replace internal portions and endpoints together. The exact joining theorem states that projected layer paths must intersect only at their joining endpoint. Compatible lengths 98 and 97 would produce 196; compatible lengths 98 and 98 would produce 197 and refute the present conjecture. Testing 197 should remain part of the investigation.

A C bitset search (`milestones/08-exhaustive-search/dfs_investigation.md`) has since exhausted end regrowth with up to 80 freed vertices at either end of every bank snake, without reaching 192 edges. It also shows that internal windows of the bank snakes are nearly frozen, and that the known 98-edge Q8 seed has no alternative optimal completion when 59 vertices are freed. Parity forbids reaching 192 by internal replacement alone. The most promising remaining routes are (a) a full classification of 97/98-edge Q8 snakes, which would decide the single-crossing (98,97) and (98,98) cases exactly, and (b) generating new 191-edge basins from scratch rather than perturbing the bank.

**Lean-checked progress on this route.** `DfsParity.lean` proves that internal rewiring of a 191-edge snake can never give 192 edges. `DfsDecide.lean` is a kernel-friendly exhaustive search with verified parity and leaf-peeling bounds, and `bank_no192_keep160` proves that no 192-edge snake shares a 160-vertex end segment with any bank snake. With version 2, `bank_no192_keep152v2` extends this to 152-vertex end segments: 2616 kernel-checked theorems in 60 modules covering about 2.2e5 search nodes, in 40 minutes on three cores, with the same axiom audit. Deeper certificates cost about 6x more per 8 freed vertices; see `milestones/08-exhaustive-search/dfs_investigation.md`.

An alternative is an induced cycle on 194 vertices, which yields a 192-edge snake after deleting one vertex. Four restricted symmetric cycle searches returned UNKNOWN; asymmetric constructions remain available. None of these routes is guaranteed to succeed.

The joint-search route now has a checked starting point: bank example 0 decomposes into compatible 96- and 94-edge Q8 paths, and its 191-edge join is Lean-checked. A new model varies both paths. It passed 42 exhaustive small-cube controls and the fixed 191-edge benchmark. Searches for (98,97), (98,98), and (96,95) each returned UNKNOWN at 120 seconds; the last used the checked pair as an unfixed hint. See `milestones/02-layer-constructions/joint_layer_investigation.md`. These results establish no exclusion of any target. Consider diverse hints or multiple-crossing models rather than treating the timeouts as structural evidence.

## Priority 2: obtain a much stronger global restriction

The square-count identity could support stronger bounds through aggregate constraints on empty and singleton squares. The universal local bound alpha >= 2 is already false, so any stronger statement needs a justified restriction or an aggregate correction.

All 131 published 191-edge examples have minimum local alpha at least three: 67 examples have minimum three, 47 have minimum four, and 17 have minimum five. This is a dataset observation, not a theorem about all long or optimal snakes. A useful investigation is whether a low-alpha configuration forces enough structural loss elsewhere to exclude sufficiently long paths. Search for counterexamples to any proposed inequality before using it in a proof.

For exact optimality, proof-producing exhaustive computation or a structural classification would be needed if analytic bounds remain weak. The current global solver returned UNKNOWN at 192 edges, and supplies no impossibility certificate. Scaling it without a symmetry argument or certifiable decomposition is an uncertain long-term route.

## Suggested division of work

- Proof contributor: independently review the completed incidence proof, then prove stronger aggregate inequalities or long-path restrictions.
- Construction contributor: diverse Q8 seeds, multiple layer crossings, and asymmetric cycle constructions.
- Extremal contributor: long-path restrictions on low-alpha configurations and aggregate square inequalities.

These are independent tasks suitable for separate branches. The current handoff assigns no person and sends no messages to collaborators.

## Evidence map and working conventions

| Material | Location |
|---|---|
| Current mathematical paper | `paper/snake9_research.tex` |
| All standard-library proofs | `work/final_lean/` |
| Bounds 237, 238, 241, 242, 245, 247, 248, 251, 254 and 255 using pinned mathlib | `work/spectral/` |
| Audits of the unconditional 241 and 242 bounds | `outputs/upper-bound-241-audit.log` (macOS), `outputs/upper-bound-241-audit-linux.log` (fresh Linux build) |
| Audit and kernel replays of the unconditional 238 bound | `outputs/upper-bound-238-audit-linux.log`, `outputs/upper-bound-238-replay-linux.log`, `outputs/aggregate-238-chain-175-linux.log` (Linux, incremental build) |
| Audit and kernel replays of the unconditional 237 bound | `outputs/upper-bound-237-audit-linux.log`, `outputs/upper-bound-237-replay-linux.log`, `outputs/aggregate-237-conditional-chain-linux.log` (Linux, incremental build); conditional 236 chain `outputs/aggregate-236-conditional-chain-linux.log` |
| Fresh 245 build and verified source hashes | `outputs/strengthened-reproduction-manifest.json`, `outputs/strengthened-reproduction.log` |
| Fresh core and incidence build | `outputs/incidence-reproduction.log` |
| Square investigation and its limitations | `milestones/03-square-incidence/square_investigation.md` |
| Layer construction and restricted exclusions | `milestones/02-layer-constructions/layer_investigation.md` |
| Competing trend fits | `milestones/01-foundations/trend_hypothesis.md` |
| Explicit witnesses and search records | `outputs/*.json` |
| Published 131-example subset | `work/bank9.json` |

The authoritative standard-library Lean sources are in `work/final_lean/`; maintained mathlib-dependent proofs are in `work/spectral/` and `work/spectral/stronger/`. Do not create divergent proof copies in `outputs/`. The authoritative paper is the existing LaTeX source. Keep implementation filenames and theorem identifiers in technical notes rather than the paper. Retain Iori Hironaka, Tommy Ma, and Steven Zhan in the author field. Contributor PDFs are snapshots; the maintained main paper is the TeX source.

A search timeout, a blocked endpoint, and a restricted exclusion cannot establish global optimality. For every claimed theorem, state exactly which assumptions are discharged. The repository is a research checkpoint, and its documentation must retain the unresolved status until a matching construction and global upper bound are verified.

## Additional local research direction: certify the radius-five obstruction

The latest experiments sharpen the remaining split-arm case. A radius-four forest is feasible with at most two interior endpoints. At radius five, the solver reports infeasibility with budgets two and three, while finding a forest with budget four. Allowing cycles restores feasibility at budget two. The saved feasible assignments passed independent Python checks; the exclusions remain uncertified. See `milestones/04-singleton-geometry/low_singleton_investigation.md` and the seven accompanying JSON records.

A checked Boolean certificate for radius five and budget two is now available. Its geometric interpretation remains a separate proof obligation; the current numerical priority is the (2,2,3) restriction described below. The general-to-normalized geometric reduction is also unfinished. The certificate for the encoded model leaves this reduction to prove. These experiments do not change the global interval.


The upstream split-arm proof, radius-three forest certificate, and ball-search records remain included; see `milestones/04-singleton-geometry/low_singleton_investigation.md`. Their restricted solver exclusions are not premises of the 245 bound.

## Integrated Boolean certificate investigation

The separately developed radius-five experiment now has a Lean-checked contradiction for an explicit core of 567 clauses and 252 Boolean variables, using 398 derived clauses. All 41 recorded cycle cuts and the general degree/endpoint clause rules are also checked. The complete interpretation of the concrete input clauses as geometric conditions on a snake is unfinished. See [the certificate investigation](milestones/06-radius-five/ball_certificate_investigation.md) for the evidence boundary and reproduction instructions.

This work does not improve the unconditional bounds. Its earlier conditional 250 arithmetic is retained as historical motivation, rather than a current strengthening target. The exclusion of the singleton-count pattern (2,2,3), the premise of the conditional bound 244, is now one of the 22 Lean-proved window exclusions behind the unconditional bound 241. The Boolean-certificate method may provide an independent route to local geometric exclusions.

## 16 October 2026 integration and organization

GitHub PR2 is integrated at b0a78f1. The main paper is now `paper/snake9_research.tex`, with both authors and the local hyperlink settings preserved. All maintained TeX files live under `paper/`; milestone folders separate investigations. Historical raw data and shared proof projects retain stable paths.

The fresh pre-DFS rebuild succeeded: 153 steps, 172 source hashes, 343 theorem axiom audits. See `milestones/05-upper-bound-245/integrated-reproduction-manifest.json`. This does not claim a new independent rebuild of every incoming DFS certificate.

The (2,2,3) work is in `milestones/07-window-223/`. Both radius-three encodings have solver proofs and independent Python replay; both large Lean translations exhausted memory. Splitting their proof declarations into separately compiled modules is the next implementation step. The geometric interpretation and arbitrary-window reduction remain required before 244 can be asserted from these encodings; (2,2,3) has since been excluded in Lean by the route of `milestones/10-window-aggregate/` (bridge, core soundness, LRAT replay), so 244 and 241 hold unconditionally.
