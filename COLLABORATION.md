# Collaborator handoff

Checkpoint: 14 October 2026. Manuscript author: Iori Hironaka.

## Where the investigation stands

The working conjecture is **a(9) = 196**, with low confidence. For n = 3,...,8, subtracting 3*2^(n-3) from the known maxima leaves 1,1,1,2,2,2. Continuing the correction in doubling blocks of three predicts 196. An equally exact additive-block fit predicts 195. The first eight values therefore do not determine the ninth, and interpolation supplies no geometric proof.

The fully Lean-checked global interval is **191 <= a(9) <= 255**. The manuscript contains a complete written square-face proof of **191 <= a(9) <= 254**, but the incidence counting has not yet been checked in Lean. No 192-edge improvement, 196-edge construction, exclusion of 197 edges, or exact optimality result has been obtained.

The most recent completed result is the universal singleton-square lemma: every vertex of every induced path in Q9 has at least one coordinate square containing no other path vertex. This is checked for all path lengths, including the short cases, and translated back from zero to arbitrary vertices. The 14-module core builds successfully.

The earlier universal two-singleton-square claim for internal vertices is false. A checked 137-edge counterexample has zero at path index 127, endpoints 145 and 288, and exactly one singleton square, {0,4,8,12}. Its distance along the path from the nearer endpoint is ten. Thus simply excluding the first few vertices near the endpoints does not repair that universal assertion. This example does not exclude a stronger statement restricted to longest paths.

## Priority 1: complete the incidence proof

This is the nearest well-defined verification milestone. It will certify 254 end to end, although it will still leave a large gap to the conjectured optimum.

For a path with v >= 2 vertices, let A_r count coordinate squares containing exactly r selected vertices. The remaining geometric obligations are:

1. There are 4,608 coordinate squares, each cube vertex belongs to 36, and no square contains four selected vertices.
2. Double counting gives A_1 + 2*A_2 + 3*A_3 = 36*v and A_0 + A_1 + A_2 + A_3 = 4608.
3. Squares with three selected vertices correspond bijectively to internal path vertices, giving A_3 = v-2.
4. Singleton squares correspond to the pairs counted locally at each vertex, giving A_1 = sum_x alpha(x) >= v.

The arithmetic consequence 2*A_0 + A_1 + 35*v + 2 = 9216 and the deduction of 254 are already checked conditionally. The task is to derive their premises from the actual snake and coordinate-square definitions.

Use `work/final_lean/SingletonSquareLemma.lean` for the proved local lemma and `SquareCountingLogic.lean` for the conditional arithmetic. `PathStructure.lean` proves the endpoint, degree, and four-cycle facts; `CubeLocal.lean` proves coordinate and translation facts. Avoid assuming a census identity as an axiom.

A possible shorter route is to prove A_3 <= v-2 by injection rather than the complete bijection; that inequality suffices for the upper-bound argument, though the equality would verify the manuscript as written.

## Priority 2: find a longer construction outside the exhausted families

A verified 192-edge example would immediately disprove the candidate optimum 191. A 196-edge example would establish the conjectured lower bound, but still would not prove optimality.

The current evidence favors widening structural diversity over repeating small changes to the same seeds:

- Every 152-vertex prefix obtained from either orientation of the 131 supplied 191-edge snakes was exhausted without reaching 193 vertices. With only 144 vertices retained, 53 searches remained unresolved at the node limit.
- Every two-vertex-deletion neighborhood of the 131 examples was excluded for a 192-edge target by the solver. Larger neighborhoods remain largely unresolved.
- The supplied 98-edge Q8 seed has no 97-edge partner under the tested exact one-crossing joining model, at either endpoint. Isometric placements of the tested truncated copy also fail. This does not classify all optimal Q8 seeds.

Useful constructive directions are structurally different Q8 seeds, constructions with multiple crossings between layers, and larger changes that replace internal portions and endpoints together. The exact joining theorem states that projected layer paths must intersect only at their joining endpoint. Compatible lengths 98 and 97 would produce 196; compatible lengths 98 and 98 would produce 197 and refute the present conjecture. Testing 197 should remain part of the investigation.

An alternative is an induced cycle on 194 vertices, which yields a 192-edge snake after deleting one vertex. Four restricted symmetric cycle searches returned UNKNOWN; asymmetric constructions remain available. None of these routes is guaranteed to succeed.

## Priority 3: obtain a much stronger global restriction

The square-count identity could support stronger bounds through aggregate constraints on empty and singleton squares. The universal local bound alpha >= 2 is already false, so any stronger statement needs a justified restriction or an aggregate correction.

All 131 published 191-edge examples have minimum local alpha at least three: 67 examples have minimum three, 47 have minimum four, and 17 have minimum five. This is a dataset observation, not a theorem about all long or optimal snakes. A useful investigation is whether a low-alpha configuration forces enough structural loss elsewhere to exclude sufficiently long paths. Search for counterexamples to any proposed inequality before using it in a proof.

For exact optimality, proof-producing exhaustive computation or a structural classification would be needed if analytic bounds remain weak. The current global solver returned UNKNOWN at 192 edges, and supplies no impossibility certificate. Scaling it without a symmetry argument or certifiable decomposition is an uncertain long-term route.

## Suggested division of work

- Proof contributor: the global incidence model and the 254 theorem.
- Construction contributor: diverse Q8 seeds, multiple layer crossings, and asymmetric cycle constructions.
- Extremal contributor: long-path restrictions on low-alpha configurations and aggregate square inequalities.

These are independent tasks suitable for separate branches. The current handoff assigns no person and sends no messages to collaborators.

## Evidence map and working conventions

| Material | Location |
|---|---|
| Current mathematical paper | `outputs/snake9_research.tex` |
| All standard-library proofs | `work/final_lean/` |
| Bound 255 using pinned mathlib | `work/spectral/` |
| Latest core build | `outputs/singleton-lean-build.log` |
| Square investigation and its limitations | `outputs/square_investigation.md` |
| Layer construction and restricted exclusions | `outputs/layer_investigation.md` |
| Competing trend fits | `outputs/trend_hypothesis.md` |
| Explicit witnesses and search records | `outputs/*.json` |
| Published 131-example subset | `work/bank9.json` |

The authoritative Lean sources are in `work/final_lean/`; do not create divergent proof copies in `outputs/`. The authoritative paper is the existing LaTeX source. Keep implementation filenames and theorem identifiers in technical notes rather than the paper. Retain Iori Hironaka in the author field. No old exported PDF is included because it predates the current source.

A search timeout, a blocked endpoint, and a restricted exclusion cannot establish global optimality. For every claimed theorem, state exactly which assumptions are discharged. The repository is a research checkpoint, and its documentation must retain the unresolved status until a matching construction and global upper bound are verified.
