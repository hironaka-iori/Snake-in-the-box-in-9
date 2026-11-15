# Round 226: residual capacity and a common Q8 construction task

The selected endpoint-24 construction is computationally excluded for two length-preserving replacement blocks of at most 43 edges each. Of 301 maximal width-44 contexts, 42 remain unresolved. Seven of these reduce to the same first-path problem in Q8: an induced path of 43 edges from 18 to 224 in a fixed 109-vertex domain, followed by the crossing to 480. No compatible complete pair or 192-edge snake has been found.

The goal remains active. This work concerns constructions; the maintained project interval remains 191 to 233. Coworkers continue the global upper-bound work, and the independent rebuild of the archived 233 argument remains pending.

## Fixed construction family

The normalized bank123 seed has 191 edges, endpoints 0 and 88, and four coordinate-8 crossings. Appending 24 requires replacing original vertices 28 and 56 at indices 7 and 143. Two open index intervals may change, retaining their anchors, all outside indices and their original edge lengths. The final target has 193 distinct vertices and four coordinate-8 crossings.

For width w, maximal intervals are [a,a+w], 0 <= a <= 6, and [c,c+w], 144-w <= c <= 142. There are 7(w-1) contexts. Padding shorter replacements with unchanged seed positions proves coverage of all shorter pairs in this family. Different seeds, endpoints, more regions and length-changing replacements are outside the exclusion.

## Completing width 43

Round 225 left 25 of 294 contexts unresolved. In 24 of them both second anchors lie in the upper face, but their available upper-face domain contains only 13 vertices in 18 cases and 14 in six cases. A zero-crossing path stays in that face, so it cannot have the required 44 vertices. The only crossing allocation is therefore (0,2). All 24 corresponding queries are infeasible; separate (2,0) queries also returned infeasible.

The remaining context, ID 114, has intervals [2,45] and [131,174] and allocation (0,1). Its first anchor is 17. Its only allowed first neighbours are 19 and 49. Forcing each choice gives an infeasible query, covering the last case. The complete native cover is 269 prior exclusions + 24 allocation exclusions + 1 first-edge exclusion = 294 contexts. `coverage43.json` preserves the source/result pins and full combined table; `logs/coverage43-review.md` independently checks the cover.

The concrete 24 face counts have passed Lean kernel reduction in `FaceCounts226`. The general zero-crossing/constant-face and capacity implications also passed Lean. Concrete prepared-domain validity, the numerical cover assembly and solver contradictions retain their separate native or independently audited status.

## Residual graph arguments

The replacement intervals have at least one retained index between them; all saved width-43 contexts have a gap of at least 52. Therefore their complete paths, including anchors, must be disjoint and nonadjacent. This gap condition is necessary when deleting the closed neighbourhood of the entire first path: adjacent intervals could have an intended anchor-to-anchor edge.

A partial first path removes its selected vertices and neighbours from the second domain. Any compatible second path lies in the remaining component of its initial anchor. The other anchor must belong to that component, which must contain enough vertices and enough of each alternating parity. Induction along the actual path proves containment; injectivity proves capacity. Extending the first prefix only deletes more residual vertices. These general facts passed Lean in `Residual226` and `ResidualCapacity226`.

The native search also restricts the second graph to the blocks on its anchor-to-anchor chain. A simple path cannot enter an off-chain block and return through the same articulation vertex. Within a chain block, adjacent entry and exit vertices force a one-edge induced segment; otherwise its two parity counts bound the segment length. Adding these bounds gives a necessary total length condition. Earlier accepted Lean lemmas support the local segment arguments. The actual low-link decomposition, segmentation and sum returned by the native program are not assembled in Lean.

The original context-22 checkpoint was transferred to this milestone by changing only its absolute input path; the input and worker bytes and all search state were preserved. A further 90 seconds brought the pruned run to 120 cumulative seconds and 3,189,946 first prefixes without exhaustion. A fresh block-bound run on context 114 processed 389,897 prefixes in 60 seconds and made 12,176 extra segment-length rejections; it also remained incomplete. Both contexts were subsequently excluded by the native covers above. Their saved frontiers are retained for evidence and should not be resumed as open cases.

## Boundary changes after the shorter family is excluded

Fix the original path and all complete-path requirements. If both replacements span 44 edges, but each keeps an original vertex immediately beside one of its anchors, shorten each interval at that end. The complete candidate does not change, and both intervals now span 43 edges. Their exclusion gives a contradiction. Thus at least one block must change both boundary-adjacent original vertices.

This argument derives actual outside agreement after contraction. It has passed Lean in `BoundaryContraction226`, with the shorter-context exclusions explicit as a premise. In this application a contraction cannot move index 7 or 143 onto an anchor: retaining vertex 28 or 56 would create a chord to appended endpoint 24. The candidate therefore remains in the covered family.

In the selected-vertex model, an original anchor-neighbour can be selected only as that anchor's unique replacement neighbour. The boundary condition is consequently encoded by requiring one block to omit both original anchor-neighbours. This cut inherits the native status of the width-43 exclusion. Together with crossing parity and face capacity, it excludes 46 of the 92 previously open width-44 contexts. The other 46 timed out; no witness or cycle cut was obtained.

## Exact upper suffixes and the common Q8 domain

Eleven of those 46 contexts have first anchors 18 and 480 in different faces. Parity and, where needed, the second face's shortage force exactly one first crossing. Although the first upper domains have different sizes, the component containing 480 is always exactly {480,488}. Its entire induced suffix is therefore either [480] or [488,480]. The corresponding lower crossing vertices are 224 and 232, and the required lower paths have 43 and 42 edges respectively.

`upper_suffixes.py` exhausts this finite enumeration. The two port models fix the entire upper suffix and retain all existing constraints. They exclude contexts 191, 200, 202 and 203, leaving 42 contexts unresolved. The port-232 option is excluded in all eleven; the port-224 branch remains unresolved for IDs 194,195,196,197,198,199,201.

These seven cases have literally identical first lower domains of 109 vertices, not merely equal sizes. Each requires a 43-edge induced path from 18 to 224, then the edge 224--480. Their first interval is [4,48]. The second replacement has 44 edges and two coordinate-8 crossings, with its own anchors, domain and parity counts. This is an exact reduction of the first-path requirement; existence of a compatible pair remains open.

The next search should grow this common Q8 prefix once, maintaining the surviving set of seven second contexts. Reject a prefix only if every second context fails a necessary condition. When the first path is complete, search the second path for each survivor and check the entire 193-vertex candidate. `shared-q8-plan.json` contains the exact domain and seven rows. This shared search is prepared, not yet executed. The other 35 open width-44 contexts remain separate.

## Verification and publication

Five new modules have accepted Lean receipts: residual containment, capacity, constant-face capacity, concrete face counts and interval contraction. Native solver exclusions have no Lean contradiction certificates. All raw per-query models remain local; their exact bytes are published in `solver-models.zip`. Incomplete direct-search checkpoints and all terminal execution receipts are preserved. No software tests were created or run.

Both existing editor manuscripts and their repository mirrors are updated and compiled before publication. Authors and hyperlink settings are preserved. The final hashes, source review, process status, frozen historical search states and contributor revision are recorded in `data/completion.json`. Preparation-time design notes saying a worker was unexecuted describe their original writing time; the later execution receipts establish what subsequently ran.
