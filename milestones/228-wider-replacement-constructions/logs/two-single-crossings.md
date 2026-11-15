# Two single-crossing replacements

This note gives the exact geometric reduction for the prepared width-45 contexts in which both replacement paths have opposite-face endpoints and their combined bit-8 crossing count is two. It is a written derivation using existing checked constructors. No compiler, solver, or search was run for this note.

## Prepared scope

In the pinned `regions45.json`, 78 initially pending contexts have crossing budget two, first anchors lower/upper, and second anchors upper/lower or lower/upper. There are 74 of the former second orientation and four of the latter. The smallest gap between the two closed replacement intervals is 49 indices. First allowed upper-face sizes range from 7 to 37, second upper-face sizes from 14 to 37. These are preparation-file counts; they do not describe the outcome of a later search batch.

The subsequent preparation considers a larger set of still-open contexts. The following reduction applies to the category above. A more general parser may also reduce contexts whose unique allocation forces one contiguous lower segment in each path. An allocation marked unsupported remains unresolved. A resource-interrupted batch and its accepted terminal rows do not establish completion of all contexts.

## Crossing allocation and lengths

For a Boolean coordinate along a path, its number of changes has the same parity as the disagreement of its endpoint values. Thus each path here has a positive odd crossing count. Their sum is two, so each has exactly one crossing. The checked coordinate-parity theorem in `EndpointParity225.lean` supplies this implication for actual paths.

Each replacement therefore consists of one lower path and one upper arm. Write an upper vertex as (256+z), with projection (z\in Q_8). Let (U_i) be the upper arm, including its fixed upper anchor and its crossing endpoint, and let (r_i) be the projection of that crossing endpoint.

The first replacement has the order

\[
L_1\ ;\ U_1,
\]

where (L_1) runs from the fixed lower anchor to (r_1), and (U_1) runs from (256+r_1) to the fixed upper anchor. For an upper/lower second replacement the order is (U_2;L_2); for a lower/upper second replacement it is (L_2;U_2).

If (U_i) contains (h_i) vertices, its upper segment has (h_i-1) edges. The lower path must have

\[
\ell_i=45-h_i
\]

edges and (46-h_i) vertices. This includes the single crossing edge in the total of 45. A singleton upper arm is allowed. In the present category (h_i\leq37), so the lower path has at least eight edges.

An exhaustive upper-arm enumeration starts at the fixed upper anchor and records an arm whenever its current endpoint has an allowed lower counterpart. It must continue beyond such a vertex: a potential crossing port can occur internally without being used as the crossing. Reverse the enumerated arm when it is an upper suffix in the actual replacement. No additional upper-length restriction is justified without a separate argument.

## Exact compatibility conditions

For fixed upper arms, the following conditions are necessary and sufficient for gluing the two replacement paths, subject to the retained-vertex restrictions below.

1. Each upper arm is an induced path with the specified fixed anchor and crossing endpoint.
2. Every vertex of (U_1) differs from and is nonadjacent to every vertex of (U_2). Include both fixed upper anchors and both upper crossing endpoints.
3. Each lower path is induced, has the required endpoints and length, and stays in its reduced lower domain. Every vertex of (L_1) differs from and is nonadjacent to every vertex of (L_2). Include fixed lower anchors and crossing ports.
4. Between a lower vertex and an upper vertex, adjacency occurs exactly when their projections coincide. The only such coincidences permitted within one replacement are its intended crossing pair. No coincidence is permitted between different replacements.

The last condition is an equality restriction on projections. Removing their (Q_8) neighbours would impose an unnecessary restriction: lower and upper vertices whose projections are adjacent have distance two in (Q_9).

Let (D_i^-) be the original allowed lower domain and (P_i) the set of projections of (U_i). The exact reduced domains are

\[
D_1'=D_1^-\setminus\bigl((P_1\setminus\{r_1\})\cup P_2\bigr),
\qquad
D_2'=D_2^-\setminus\bigl((P_2\setminus\{r_2\})\cup P_1\bigr).
\]

Both lower endpoints must survive these restrictions. The exemption for one's own port does not exempt a coincidence with the other upper arm. The fixed lower anchor is not an additional exempted projection. Here it differs from the crossing port because the lower path has positive length.

The interval gap is at least 49. Consequently every pair of vertices belonging to different replacement blocks, including their anchors, is nonconsecutive in the assembled path. There is no cross-block anchor adjacency to preserve.

## Retained vertices and gluing

The original allowed domains exclude all retained vertices except the block's own anchors and exclude neighbours of all retained vertices except those own anchors. They also impose the restrictions needed to append vertex 24. An induced replacement with unchanged anchors can meet the own-anchor neighbours only at the intended adjacent positions; local inducedness handles this exception. The two blocks' anchors must still obey the cross-block separation above.

For each block, restrict its upper arm to its (Q_8) projections. The reduced-domain condition says that the two constituent (Q_8) paths have exactly their intended endpoint in common. This is the compatibility premise of the accepted `LayerJoining.join` constructor. Reversal or exchange of face labels gives the upper/lower orientation in the undirected cube. The result is an actual induced one-crossing replacement, without assuming that its full concatenation is already induced.

The local replacements, retained-vertex agreement and separation, and cross-block separation then satisfy the accepted `Simultaneous225.replaceTwoBlocks` conditions. This builds the entire path. Replacing two 45-edge intervals preserves the original 191-edge length; appending 24 gives 192 edges and 193 vertices when its retained and replacement restrictions hold. The two replacement crossings and two retained crossings give four in total. This states a construction criterion, not an attained witness.

Conversely, every actual candidate in this allocation restricts to arms and lower paths of the stated lengths and satisfies these conditions. Exhaustive enumeration of the arms therefore reduces this allocation to the lower-pair tasks. This converse also requires the original domain preprocessing to preserve every candidate. In particular, anchor-protected degree peeling and component restriction need their usual path-preservation justification; merely listing the resulting allowed vertices does not establish enumeration completeness.

## Preparation review and omitted boundary condition

The inspected `prepare_lower_pairs.py` uses full upper-pair separation, removes the other arm's projections, and records both lower domains, ordered endpoint pairs, and edge lengths in its exact-task key. These are the required fields when no further template-dependent condition is retained. Domain-subset dominance is valid only with the same endpoint pairs, lengths, and lower-pair separation relation.

One own-arm mask in the inspected version is too permissive for exact reconstruction. In `templates`, `low - (projections - {s,t})` exempts both lower endpoints. For a single upper arm, only one of them is a crossing port. The exact set of exempted ports is `{s}` when there is an upper prefix, together with `{t}` when there is an upper suffix. A fixed lower anchor without an adjacent upper piece must remain subject to the projection exclusion. This finding was reported to the parent. The inspected hash is recorded below; a later corrected version must be assessed against its own hash.

The permissive version enlarges the lower task. Its infeasibility still excludes all intended candidates. A satisfying lower task would require the exact port restriction before gluing could be concluded.

The parent subsequently counted the potential offending projection in the saved 2,141 unfiltered configurations and 672 boundary-filtered configurations. The reported count was zero in both. Thus this general-helper issue does not change these literal configurations. This observation is a native saved-data result, not a Lean theorem; the source remains pinned during the active worker, and the stricter exemption should be used before general reuse. The inspected saved-data hashes are `36db50e0498768de092cbb2528bf32488f1133c0f591702462bcf1ab52621a88` for `lower-pairs.json` and `2a0212a2034039b3ddddb1c6f788b6d9761fdf6cd0efbbb3c837b749ebf38503` for `boundary-lower-pairs.json`.

The current reduced models deliberately omit the earlier condition that at least one block changes both old boundary-adjacent vertices. This also enlarges the model, so reduced-model infeasibility covers the intended boundary-filtered candidates. No additional boundary clause is needed in the current task key. If that condition is later imposed, its instantiated content must be retained when identifying tasks: different upper arms can satisfy or disable parts of it even when the lower domains and lengths agree.

## Evidence boundary

The general coordinate-parity, one-crossing joining, and simultaneous-replacement components already have accepted Lean proofs. No new generic module is needed for this reduction. The present note does not claim a checked bridge from the literal 228 domains and enumeration code to those theorems. The native template enumeration, preprocessing preservation, individual reduced solver receipts, and any final assembled witness remain separate evidence. Unsupported allocations and interrupted jobs provide no exclusion.

## Input pins

All paths are relative to `E:/Snake-in-a-box`.

| File | SHA-256 |
| --- | --- |
| `milestones/228-wider-replacement-constructions/data/regions45.json` | `e64a1de95fe6354ec64e8a5bfc51457bafc262f581df1188a1683978c26d5bb9` |
| `milestones/228-wider-replacement-constructions/scripts/prepare_width.py` | `391211994dabe1770ea0db0cd0be97f461f4262736a70f294a31c35d49bdc4be` |
| `milestones/228-wider-replacement-constructions/scripts/prepare_lower_pairs.py` (inspected version) | `718f8fd64159e5d621ae5367b16a3b07943efdf6a902a07fff664dd7fc120f92` |
| `milestones/188-dimensional-constructions/lean/LayerJoining.lean` | `30687e190d96818b64569e90faaff50eba28acf7698e4ffa8c6d89d8fe640a74` |
| `milestones/225-replacement-widths/lean/Simultaneous225.lean` | `ce2129459ff1cc31f2cce81c599a0c7c25bc31fb07dac3c5aded95ccadf71882` |
| `milestones/225-replacement-widths/lean/EndpointParity225.lean` | `f8fc9fa62313f890ee791524d1c421fc85ae2270e4f2e11d663d5055413aacf7` |
