# Compatible second paths: prior work and unresolved construction

The most direct unresolved construction with the saved98-edge parent is a93-edge partner at either endpoint, giving192 edges in Q9. The97-edge partner problem for this same parent already has two recorded solver exclusions. Those exclusions are stronger than an isometric-copy census, but neither has a Lean contradiction certificate. Searching for a different98-edge parent is therefore justified for a196-edge single-crossing construction; it is an additional discovery stage that is unnecessary for the still-open192 target.

This review read every line4200–4710 and5100–5630 of `paper/snake9_research.tex`, the construction appendix through9515, the original layer records and source, and the relevant construction notes188–194 and199 cited by those sections. The paper hash at the start was `765c574597a22b287310587b8efa31f6e31bd1d2751d7a54fc8b309d5255870b`. No search, compiler, solver or software tests were run. Historical statements below retain their original scope; this review does not establish uniqueness or an exhaustive inventory of every experiment in the repository.

## Exact fixed-parent problem

For a joining endpoint \(t\) of the saved path \(P\), the permitted second-layer base graph is

\[
Q_8\bigl[\{0,\ldots,255\}\setminus(V(P)\setminus\{t\})\bigr].
\]

It has158 vertices, including its prescribed endpoint \(t\). The other endpoint is free. Only the other98 parent vertices are forbidden; their neighbours must not all be forbidden, because cross-layer adjacency is equality of base vertices. A93-edge partner uses94 vertices and produces \(98+93+1=192\) edges. A97-edge partner uses98 vertices and would produce196.

The source `work/layer_search.py`, function `solve_complement`, translates each chosen endpoint to0, calls `exact_search.model(8,target,symmetry=False)`, and forbids exactly the translated parent vertices other than0. `work/exact_search.py` forces0 as a path endpoint and uses a dummy-vertex circuit for connectivity. It requires every selected cube edge to lie in the path. Thus the recorded partner query permits arbitrary partner shapes; it is not limited to copies or truncations of the seed. This was a source inspection, without a new audit or rerun of the solver encoding.

| Recorded family | Result | Evidence |
|---|---|---|
|97-edge endpoint truncations of isometric copies of the same parent; all endpoint joins and coordinate permutations|322,560 placements; minimum intersection15 instead of the required1|`outputs/layer_search.json`, `orbit`|
|Arbitrary97-edge partner at endpoint0|INFEASIBLE,0.859seconds|Same file, first `complement_search` entry|
|Arbitrary97-edge partner at endpoint78|INFEASIBLE,0.421seconds|Same file, second entry|
|Arbitrary93-edge partner at endpoints0 and78|UNKNOWN after30.047 and30.062seconds|`outputs/layer_threshold.json`|
|Arbitrary92- or91-edge partner at either endpoint|All four queries UNKNOWN after about30seconds each|Same threshold file|
|Degree-at-most-two complement relaxation|106 selected vertices admitted at either endpoint|`outputs/complement_relaxation.json`|

The97-edge solver exclusions also exclude longer rooted partners by taking a prefix, subject to the same solver-evidence qualification. They do not exclude93-edge partners. The degree relaxation is too weak to settle either target and permits disconnected selections.

`milestones/02-layer-constructions/layer_investigation.md` explains these scopes. The later `milestones/08-exhaustive-search/dfs_investigation.md`, section5, records a separate97-edge partner DFS unresolved at three billion nodes. That unfinished independent attempt does not supersede the earlier solver exclusions or certify them. Its rigidity observations about retained prefixes also do not classify all98-edge parents.

Decisive input hashes:

- `outputs/snake8_witness.json`: `2b328e537867b097316150be170a9af68e5af492bc7667d3b781b77d39e4e2f5`
- `outputs/layer_search.json`: `67afb486c0c6b609b55db8277750710f7539f8a510c0cb8032d93e725393e3d4`
- `outputs/layer_threshold.json`: `553f53a9ff26302c8ecd512e1eed6598c9eeec5546e4b52df8f37685aef7e2a8`
- `work/layer_search.py`: `6e2b4c4c87b6bfcf7ccfa78c196cd122ee09655bb76f1a3892090dba4974a29c`

## Related layer searches that remain open

`milestones/02-layer-constructions/joint_layer_investigation.md` records120-second UNKNOWN runs with both paths variable for lengths(98,97),(98,98), and(96,95). The last uses the checked compatible(96,94) pair only as an unfixed hint. The(96,94) join is a known191-edge example, not a new class or record.

The fixed98-edge **middle** query in `milestones/191-coloured-replacements/data/optimal-middle-8-target192.json` is different: it uses two crossings and two opposite-face outer components, including possible singleton components. It remains UNKNOWN after180seconds. It is not an exclusion or solution of the one-crossing93-edge partner problem.

Likewise, the77-vertex complement query in paper lines5571–5584 concerns a49-vertex path in Q7, disjoint from a51-vertex Q7 parent. It is one step towards a100-vertex paired Q8 face and still requires an opposite-face Q9 completion. It must not be confused with the158-vertex Q8 complement considered here.

## Tailored97-edge replacements: avoid repeating restricted failures

The common95-edge middle of the saved191-edge family has fixed endpoints at distance three. Replacing it by97 edges while retaining its two outer components would produce193 edges. The first context permits162 Q8 vertices. The unrestricted fixed-context query remains UNKNOWN: see `189-middle-replacements/data/context00-middle97.json` and the later `191-coloured-replacements/data/omissions-at-most-96-context00.json`.

The following narrower approaches already have substantial negative evidence:

- Keeping the internal31- and15-edge pieces and replacing only their47-edge Q7 middle by49 is solver-infeasible even after removing the external Q9 restrictions. Evidence: `189-middle-replacements/data/nested00-relaxed-middle49.json`; the externally restricted instance is `nested00-middle49.json`. No Lean contradiction certificate is recorded.
- All applicable endpoint-preserving placements of the known97-edge truncation against each of84 saved contexts retain at least23 forbidden overlaps. This is a complete census for that seed-placement family, not all97-edge paths. Evidence: `189-middle-replacements/data/known97-replacements.json` and `MATHEMATICAL_NOTE.md`.
- Contiguous internal replacements through42 deleted vertices and all two-position changes were completely enumerated without improvement. Size43 was only partly searched. Evidence: `189-middle-replacements/data/local-repair-17-48.json` and `two-changes.json`.
- Successive native exclusions cover fixed-endpoint replacements omitting at most seven original vertices. Consequently any97-edge replacement of the common95-edge path must omit at least eight and add at least ten, under those computational exclusions. The at-most-eight query remains UNKNOWN. Evidence: `190-exchange-constraints/data/five-omissions-cycle-cuts.json`, `two-intervals-five-omissions.json`, and `191-coloured-replacements/data/omissions-at-most-{6,7,8}.json`. These are not complete Lean contradiction certificates.
- The known97-edge seed placement retaining52 original vertices omits44 and has30 forbidden overlaps in the first outer context. It gives a valid unrestricted97-edge path, not a compatible Q9 improvement. Evidence: `190-exchange-constraints/data/nearest-replacement.json` and `MATHEMATICAL_NOTE.md`.

The common-path overlap range and fixed-context problem are separate. A close unrestricted replacement might still violate the external compatibility conditions. The later square-substitution and short-rerouting exclusions in rounds192–194 also concern specified move families; they do not settle an arbitrary compatible93-edge partner or arbitrary97-edge replacement.

## Recommended next direct step

For the first improvement beyond191, the clearest unresolved target is the two endpoint cases for a93-edge induced path in the158-vertex complement of the already checked98-edge parent. Keep the second endpoint free and impose no closeness-to-seed, fixed-prefix or isometric-copy restriction. A positive result immediately supplies a192-edge construction through the existing joining theorem. A negative result would need complete evidence for each endpoint; the current30-second UNKNOWN records provide none.

This recommendation is based on the directness and unresolved scope of the target, not a measured claim that it is computationally easier. A new method or a recorded bounded continuation would be preferable to repeating the old unchanged30-second run. The stronger196 target requires either a different98-edge parent, a different construction with multiple crossings, or a correction to the old97-partner exclusions after independent review. Continuing the current different-parent search is mathematically justified, but a new parent alone still requires a compatible partner. The inspected history does not justify treating parent diversity as the only remaining route to192.

The fixed-context95-to97 replacement is a second direct unresolved route, giving193 if successful. Its nested and near-seed variants should not be repeated within their already excluded scopes. No relative runtime ranking between this route and the93-edge complement target has been established.

## Follow-up: reusable degree model with cycle exclusions

The reusable cycle-exclusion loop is in `milestones/190-exchange-constraints/scripts/cycle_cuts.py`. It selects vertices, conditionally imposes their exact induced degrees, enumerates connected components of each returned selection, and excludes every separate cycle \(C\) by \(\sum_{v\in C}x_v\le |C|-1\). The concrete190 query additionally fixes two endpoints,98 selected vertices,91 retained old vertices, at most two deleted internal edges, an exchange identity and1792 square inequalities. Those replacement-specific restrictions must all be removed when adapting it to an arbitrary compatible partner. Its saved five-omission query was already INFEASIBLE in its first relaxation, with no dynamic cycle cut added; that result does not show cycle-cut performance on the complement problem.

For variable endpoint indicators, the more direct source is `milestones/192-moving-ports/scripts/joint_replacement.py`. Its generic degree portion uses Boolean selection \(x_v\), endpoint indicator \(e_v\le x_v\), exactly two endpoints, and

\[
x_v=1\ \Longrightarrow\ \sum_{u\sim v}x_u=2-e_v.
\]

For the93-edge partner, restrict selection to the158 allowed vertices, require94 selected vertices, and fix \(x_t=e_t=1\) at the joining endpoint. Leave the second endpoint free. The displayed degree equation must remain conditional on selection: imposing it as an unconditional equation with zero right-hand side at an unselected vertex would wrongly forbid its adjacency to selected vertices. No seed-overlap, omission, exchange, or Q9 crossing-count condition belongs in this complement query. The192 script's endpoint-corrected exchange identity is therefore also discarded.

Every selected component then has degree at most two and no isolated vertex. Exactly two vertices have degree one, so the selection consists of one path containing both endpoints, plus zero or more disjoint cycles. The endpoint at \(t\) identifies the path component. If no cycle remains, the selection is the required induced94-vertex path. Otherwise the190 component loop supplies valid exclusions of the observed cycles and the model is solved again. A resource limit while cycles remain is UNKNOWN, even if the degree relaxation returned a feasible selection. Any final path still needs direct all-pairs and joining checks. A terminal solver exclusion remains uncertified unless independently translated into an accepted proof.

Since the allowed graph is bipartite and the target has94 vertices,47 vertices of each colour is necessary. The second endpoint has the colour opposite to \(t\). These restrictions follow from the path-plus-even-cycles structure and may be included without fixing its location. Coordinate-square inequalities are also valid optional initial cuts; they do not remove the need to handle longer cycles.

The recorded93-partner experiment did not use this formulation: `work/layer_threshold.py` calls `solve_complement`, which calls the auxiliary-circuit model in `work/exact_search.py`. Neither `outputs/layer_threshold.json` nor the inspected layer notes records a degree-and-cycle-cut93-partner run. The historical190 and192 uses address different replacement problems. This is therefore a specifically identified alternative to the documented old93 query; absence of a record in this bounded review is not a claim that no other contributor has ever attempted it. No adaptation or solver run was performed here.

Follow-up source pins: `190-exchange-constraints/scripts/cycle_cuts.py` has SHA-256 `e8c435de9dcaf91926cd4f000a3f0ce0d063e0fa13b9b381542373dc0fdb82c2`; `192-moving-ports/scripts/joint_replacement.py`, `83837296b1d5ebb7359f0e8909585149c0ac816d1e4fc0302eee330d07e4fee2`; `work/layer_threshold.py`, `06b6d7d7393f4fba4e49d0d596711bb96de98ba2aa9f2279c0713003fc35222f`; and `work/exact_search.py`, `51fb9b7d6f43b9bdf520b2eff4a15c6ae5c9f875db42cc0a0d2fe4fbf9d1cdb6`.
