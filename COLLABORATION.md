# Collaborator handoff

Checkpoint: 15 October 2026. Manuscript author: Iori Hironaka.

## Where the investigation stands

The working conjecture is **a(9) = 196**, with low confidence. For n = 3,...,8, subtracting 3*2^(n-3) from the known maxima leaves 1,1,1,2,2,2. Continuing the correction in doubling blocks of three predicts 196. An equally exact additive-block fit predicts 195. The first eight values therefore do not determine the ninth, and interpolation supplies no geometric proof.

The fully Lean-checked global interval is now **191 <= a(9) <= 254**. The square-face bound is checked end to end using an anchored-incidence identity; the independent spectral argument still supplies the weaker bound 255. No 192-edge improvement, 196-edge construction, exclusion of 197 edges, or exact optimality result has been obtained.

The strongest completed global bound is 254. The proof sums each square from its four corners, uses the checked singleton-square lemma, and injects selected two-edge corners into internal path vertices. The proof audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The exact optimum remains open.

The earlier universal two-singleton-square claim for internal vertices is false. A checked 137-edge counterexample has zero at path index 127, endpoints 145 and 288, and exactly one singleton square, {0,4,8,12}. Its distance along the path from the nearer endpoint is ten. Thus simply excluding the first few vertices near the endpoints does not repair that universal assertion. This example does not exclude a stronger statement restricted to longest paths.

## Completed milestone: incidence proof

The formerly pending upper-bound verification is complete. `work/spectral/SquareIncidence.lean` proves the following quantities directly from the cube and path definitions:

- E: total number of empty squares counted from each possible corner.
- T: total singleton incidences, counted at their selected vertex.
- W: total selected centers with both neighbors in a distinct coordinate pair selected.

For a path on v vertices, the checked identity is

`2*E + 4*T + 144*v = 36864 + 4*W`.

The checked estimates T >= v and W <= v-2 (for v >= 2) give v <= 255, hence at most 254 edges. The proof handles all path lengths. It uses the same snake definition as the 191-edge witness and assumes no census equation.

This replaces the need to certify all original canonical-square bijections before establishing 254. The old conditional arithmetic module remains as a record of the first approach. The exact canonical census equalities have not separately been certified; they are unnecessary for the new theorem. The paper now presents the checked proof.

Reproduce with `python work/spectral/verify_incidence.py --mathlib-dir /path/to/mathlib --fresh-core` after preparing the pinned dependency. The next priorities concern improving the mathematics beyond 254.

## Immediate proof target: certify the radius-five obstruction

The latest experiments sharpen the remaining split-arm case. A radius-four forest is feasible with at most two interior endpoints. At radius five, the solver reports infeasibility with budgets two and three, while finding a forest with budget four. Allowing cycles restores feasibility at budget two. The saved feasible assignments passed independent Python checks; the exclusions remain uncertified. See `outputs/low_singleton_investigation.md` and the seven accompanying JSON records.

This is the most concrete next proof direction: obtain a checkable exclusion certificate for radius five and budget two, then prove that a genuine snake with a one-singleton root far from both endpoints maps into that model. The general-to-normalized geometric reduction is also unfinished. A certificate for the encoded model alone would leave this reduction to prove. These experiments do not change the global interval.

## Construction priority: find a longer construction outside the exhausted families

A verified 192-edge example would immediately disprove the candidate optimum 191. A 196-edge example would establish the conjectured lower bound, but still would not prove optimality.

The current evidence favors widening structural diversity over repeating small changes to the same seeds:

- Every 152-vertex prefix obtained from either orientation of the 131 supplied 191-edge snakes was exhausted without reaching 193 vertices. With only 144 vertices retained, 53 searches remained unresolved at the node limit.
- Every two-vertex-deletion neighborhood of the 131 examples was excluded for a 192-edge target by the solver. Larger neighborhoods remain largely unresolved.
- The supplied 98-edge Q8 seed has no 97-edge partner under the tested exact one-crossing joining model, at either endpoint. Isometric placements of the tested truncated copy also fail. This does not classify all optimal Q8 seeds.

Useful constructive directions are structurally different Q8 seeds, constructions with multiple crossings between layers, and larger changes that replace internal portions and endpoints together. The exact joining theorem states that projected layer paths must intersect only at their joining endpoint. Compatible lengths 98 and 97 would produce 196; compatible lengths 98 and 98 would produce 197 and refute the present conjecture. Testing 197 should remain part of the investigation.

An alternative is an induced cycle on 194 vertices, which yields a 192-edge snake after deleting one vertex. Four restricted symmetric cycle searches returned UNKNOWN; asymmetric constructions remain available. None of these routes is guaranteed to succeed.

The joint-search route now has a checked starting point: bank example 0 decomposes into compatible 96- and 94-edge Q8 paths, and its 191-edge join is Lean-checked. A new model varies both paths. It passed 42 exhaustive small-cube controls and the fixed 191-edge benchmark. Searches for (98,97), (98,98), and (96,95) each returned UNKNOWN at 120 seconds; the last used the checked pair as an unfixed hint. See `outputs/joint_layer_investigation.md`. These results establish no exclusion of any target. Consider diverse hints or multiple-crossing models rather than treating the timeouts as structural evidence.

## Global proof priority: obtain a much stronger restriction

The square-count identity could support stronger bounds through aggregate constraints on empty and singleton squares. The universal local bound alpha >= 2 is already false, so any stronger statement needs a justified restriction or an aggregate correction.

All 131 published 191-edge examples have minimum local alpha at least three: 67 examples have minimum three, 47 have minimum four, and 17 have minimum five. This is a dataset observation, not a theorem about all long or optimal snakes. A useful investigation is whether a low-alpha configuration forces enough structural loss elsewhere to exclude sufficiently long paths. Search for counterexamples to any proposed inequality before using it in a proof.

For exact optimality, proof-producing exhaustive computation or a structural classification would be needed if analytic bounds remain weak. The current global solver returned UNKNOWN at 192 edges, and supplies no impossibility certificate. Scaling it without a symmetry argument or certifiable decomposition is an uncertain long-term route.

The latest local result narrows one-singleton configurations: under the explicitly stated internal-pair-vertex premises, the two continuations must use opposite coordinates of the exceptional pair. This is Lean-checked. A separate checked 60-vertex, 14-component forest satisfies all the radius-three degree and acyclicity requirements, so those requirements alone cannot exclude the remaining case. The endpoint-proximity conjecture still needs global connectivity or constraints involving higher-weight vertices; see `outputs/low_singleton_investigation.md` before pursuing a purely local proof.

## Suggested division of work

- Proof contributor: certify the radius-five obstruction and the geometric reduction, while independently reviewing the completed incidence proof.
- Construction contributor: diverse Q8 seeds, multiple layer crossings, and asymmetric cycle constructions.
- Extremal contributor: long-path restrictions on low-alpha configurations and aggregate square inequalities.

These are independent tasks suitable for separate branches. The current handoff assigns no person and sends no messages to collaborators.

## Evidence map and working conventions

| Material | Location |
|---|---|
| Current mathematical paper | `outputs/snake9_research.tex` |
| All standard-library proofs | `work/final_lean/` |
| Bounds 254 and 255 using pinned mathlib | `work/spectral/` |
| Fresh core and incidence build | `outputs/incidence-reproduction.log` |
| Square investigation and its limitations | `outputs/square_investigation.md` |
| Layer construction and restricted exclusions | `outputs/layer_investigation.md` |
| Competing trend fits | `outputs/trend_hypothesis.md` |
| Local restrictions and uncertified ball experiments | `outputs/low_singleton_investigation.md` |
| Explicit witnesses and search records | `outputs/*.json` |
| Published 131-example subset | `work/bank9.json` |

The authoritative Lean sources are in `work/final_lean/`; do not create divergent proof copies in `outputs/`. The authoritative paper is the existing LaTeX source. Keep implementation filenames and theorem identifiers in technical notes rather than the paper. Retain Iori Hironaka in the author field. No old exported PDF is included because it predates the current source.

A search timeout, a blocked endpoint, and a restricted exclusion cannot establish global optimality. For every claimed theorem, state exactly which assumptions are discharged. The repository is a research checkpoint, and its documentation must retain the unresolved status until a matching construction and global upper bound are verified.

## Publication status

The manuscript, core Lean sources, mathlib-dependent proofs, reproduction instructions, witness data, and existing experiments are included. The manuscript compiles, its author is Iori Hironaka, and its authoritative source is in `E:\Snake-in-a-box`. During this handoff, all four primary witnesses and all 131 bank examples passed the independent all-pairs verification. No new research claim was promoted to a theorem. Further research is stopped at this handoff pending a continuation request.
