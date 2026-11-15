# Round 224 region and joint-model review

Review date: 15 November 2026. Finding: no invalid exclusion was found within the stated fixed-seed, equal-length two-block model, conditional on the round-193 native closure premise for the mutual-contact restrictions. The geometric domain reductions themselves are necessary without that closure premise.

## Material inspected and limits

Read all 48 lines of `scripts/prepare_regions.py`, all 75 lines of `scripts/joint_regions.py`, the complete round-193 mathematical note, the current two-block argument in `logs/two-block-review.md`, and the manuscript's replacement/closure discussion at lines 4913–4975. Parsed every context and part in `data/regions.json` and independently reconstructed the geometry described below. The large JSON was inspected as structured data, rather than claiming a manual reading of its 110539 text lines.

Only this review file was written. No optimizer, compiler or software tests were run. The read-only geometric calculation was the explicitly permitted independent mathematical audit. It neither replayed the round-193 enumeration nor certified a native solver contradiction. The new Lean modules were outside this assigned model review.

| Reviewed artifact | SHA256 |
|---|---|
| `scripts/prepare_regions.py` | `ef195a56539e9c5935c5877e4f9f78c56c0d66f22e518e8fbd2fdf46864583d3` |
| `scripts/joint_regions.py` | `dba35090136370b5984b6d58e7997e769a43008e807a830c4c3eb9b59ff285e6` |
| `data/regions.json` | `29ff765b61e6a306b18a81b8745d91cdc27d427a3ccf400344a6366ef4f40bad` |
| Pinned round-223 `data/joint-d4.json` | `3df4967aaf726c4db222d577f13507b227425c82a57607a46354905cd2f91932` |

The region record's source and preparation-script pins agree with those files. Seed membership and normalization use the round-223 seed previously reviewed in `223-coupled-four-crossings/logs/model-review.md`; this review additionally checked its 192 distinct vertices and every unordered adjacency pair directly.

## Window coverage and crossing counts

The seed has exactly four bit-8 crossings, at edge indices 46, 130, 163 and 177. Vertex 24 is absent. Its selected neighbours occur at indices 7, 143 and 191, containing vertices 28, 56 and 88 respectively. Appending 24 after 88 therefore requires the first two blockers to disappear from their original positions and forbids every other replacement contact with 24.

Any block containing index 7 strictly inside and having at most 33 edges is contained in a window $[a,a+33]$ with $0\le a\le6$. For an original block $[r,s]$, one may take $a=\max(0,s-33)$. Any analogous block containing index 143 is contained in $[c,c+33]$ with $111\le c\le142$, taking $c=s-33$. Padding uses unchanged original positions and preserves the replacement's length and the final path. The maximal windows remain disjoint because the first ends by 39 and the second begins no earlier than 111. Thus the 224 pairs cover every two-block replacement in the requested short-block class; they are overlapping search contexts, not a disjoint partition of paths.

Independent finite reconstruction found 203 possible original short intervals containing 7 and 528 containing 143, with no interval omitted from this maximal cover. The JSON lists exactly the expected $7\cdot32=224$ maximal pairs in the expected order.

Every first window lies wholly in the lower face and contains no original crossing. Every second window contains exactly one original crossing, either index 130 or index 163, and has anchors in opposite faces. Consequently three crossings remain fixed outside the windows. Appending 24 to 88 adds no bit-8 crossing. For a four-crossing result, the replacement crossing counts sum to one. The first count is even and the second is odd, so they must be zero and one. Restricting the first domain to the lower face and imposing these crossing counts loses no path in the specified four-crossing class.

This coverage does not include unequal-length replacements, blocks longer than 33 edges, a different appended endpoint, a different seed alignment, or targets with a different total crossing count.

## Static domains and independent reconstruction

For each part, its interior cannot equal a retained vertex, meet vertex 24 or any neighbour of 24, or be adjacent to a retained vertex other than its own two anchors. The preparation script removes precisely these forbidden possibilities and then restores the two anchors. Restoring anchors is necessary because their intended outside neighbours remain selected. The other block's anchors remain forbidden contacts. Both blocks lie far apart in index, so no intended edge connects their replacements.

A nonanchor on a valid replacement must have two neighbours on that replacement. Repeatedly deleting nonanchors of current domain degree below two is therefore sound. The anchors are exempt. A valid replacement is connected to its first anchor, so discarding every other remaining component is also sound. Failure to retain the second anchor, fewer than 34 remaining vertices, or fewer than 17 vertices of either parity excludes a 33-edge replacement. The two anchors have opposite parity, so the 17/17 requirement is necessary.

The independent calculation built adjacency by Hamming distance, reconstructed all retained sets and initial masks, computed the terminal degree core by synchronous deletion rather than the script's queue order, and computed the anchor component separately. It also checked each saved peeling step against its then-current degree and reconstructed every contact set, rejection list and context status.

- All 224 contexts and all 448 initial/final domains agreed.
- All 5815 saved peeling steps were valid and reached the same terminal cores.
- Every part's anchors, interval, crossing count, contact candidates and rejection reasons agreed.
- There are 171 statically excluded contexts and 53 pending contexts.
- Every one of the 171 static exclusions has at least one geometric reason: disconnection, insufficient size or insufficient parity capacity. None relies solely on `NO_CROSS_CONTACT`.
- At part level, the saved counts are 188 disconnection reasons and 167 each of size, colour and no-contact reasons. These overlap and must not be summed as numbers of excluded contexts.

No discrepancy was found.

## Mutual contact and its exact dependency

The candidate contact sets correctly include equality as well as adjacency with the *original open interior* of the other window. They are not restricted to vertices omitted from the final selected set, which would be unsound because a vertex may move between blocks.

The argument is conditional on the saved bank being closed, up to cube isometry and reversal, under every equal-length replacement of at most 33 edges, and every bank member having blocked endpoints. If the first replacement alone were induced, closure would put that intermediate path in the bank family. The second replacement would then be another allowed short move whose induced result is the assumed simultaneous path. Closure would make its endpoint blocked, contradicting extension by 24. Reversing the order gives the other required contact. Equal lengths preserve the other block's indices and anchors.

Final inducedness already rules out internal replacement defects and contacts with fixed positions. Thus the failure of each intermediate path must be a collision or adjacency between that new interior and the old interior of the other block. This justifies both the empty-contact static rejection and the joint model's requirement to select at least one contact candidate per part.

The native round-193 closure census is the essential finite premise. The generic geometric and iteration implications do not certify that census. The longer cutoff from a single-move-plus-extension experiment cannot substitute for the 33-edge closure cutoff. The contact restrictions must retain this conditional scope in any resulting exclusion statement.

## Joint model and witness assembly

Each part selects 34 domain vertices, including both anchors. Selected anchors have selected degree one; every selected nonanchor has selected degree two. Unselected vertices impose no degree restriction. These are necessary for the intended induced 33-edge path. The even-colour count is 17, and the vertical-edge conjunction constraints correctly count selected bit-8 edges.

Every equality or cube adjacency between the two selected parts is prohibited. This includes anchor pairs. It is valid here because the two windows are disjoint and separated by a long retained interval, so no cross-part pair has consecutive final indices. Retained-position contacts have already been handled by the domains.

Before cycle cuts, a part may consist of the anchor-to-anchor path together with disjoint cycles. With exactly two degree-one vertices, both anchors belong to the same path component. The trace from the first anchor is therefore determined until the second anchor. Every remaining component has degree two. Requiring at least one vertex of an observed cycle to be absent is valid for any induced replacement path. Once no cycles remain, all 34 selected vertices belong to the replacement, so its length is exactly 33.

The assembly at line 66 includes both replacement anchors exactly once, retains the original positions outside the open interiors, and appends 24. Its length is 193 vertices. The subsequent distinctness, all-pairs adjacency and four-crossing assertions check the concrete candidate before saving a witness. Their presence was reviewed; no witness execution was reproduced in this review.

Initial serialized models omit later dynamic cycle cuts. Reproducing a query requires the initial model together with its recorded cycle cuts. The source records that distinction appropriately.

## Reporting caveat and observed result state

At line 73, `COMPLETE_COVERAGE` means every context has a result entry. That label alone does not imply every context was excluded, because entries may be `UNKNOWN` or `TIME_LIMIT`. Any exclusion claim must inspect the individual statuses. No model change is required to interpret the current saved result accurately.

The read-only `pair33.json` snapshot observed during this review contained all 224 entries: 171 `STATIC_EXCLUDED` and 53 `INFEASIBLE`, with no witness and a saved total of approximately 4.453 seconds. This is a report of the saved native outcomes, not an independent solver replay or contradiction certificate. The model review supports their stated mathematical scope; it does not upgrade them to Lean-certified numerical exclusions or a global upper bound.
