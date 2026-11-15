# Round 229 preparation review

Result: no blocking defect found in the inspected width-46 preparation. This is a bounded source and exact finite-data review. It does not certify current solver outcomes or replace the native width-45 exclusion premise by a Lean proof.

## Scope and reconstruction

Read all of `prepare_round.py`, `prepare_width.py`, `prepare_baseline.py`, `prepare_lower_pairs.py`, `prepare_boundary_pairs.py`, `transfer_tasks.py`, `prepare_pair_model.py`, `joint_boundary.py`, and `pair_cp.py`. Independently reconstructed the immutable data without importing or executing those producers or a solver. No compiler, software tests, live-result inspection, or process changes were performed.

The independent reconstruction checked 23 embedded source/data hashes. The copied `coverage45.json` is byte-identical to round 228. Its status is `COMPLETE_NATIVE_EXCLUSION`, its width is 45, and its 308 context records have only the five completed exclusion statuses. Its pinned dependencies match current bytes. The previous closure is an explicit native premise; this review does not repeat all earlier solver-model audits.

The data reconstruction completed in approximately two seconds. A separate pointer-typed Windows measurement with all principal JSON inputs and the prior task data loaded recorded a peak working set of 60,829,696 bytes, below 256 MiB. The first untyped memory call returned no measurement; its zero value is not evidence of memory consumption.

## Width and initial domains

The seed has 192 distinct vertices, is induced, starts at 0, ends at 88, and has four coordinate-8 crossings. The vertices adjacent to the proposed appended endpoint 24 occur exactly at indices 7, 143, and 191. Index 191 provides the intended final edge.

The 315 contexts are exactly

\[
 [a,a+46],\quad[c,c+46],\qquad 0\le a\le6,\quad98\le c\le142.
\]

Every pair of replacements of length at most 46 whose open interiors remove the two unwanted endpoint neighbours can be extended to a listed pair by retaining additional original path edges. For a block ending at index \(r\), choose the enlarged first start \(\max(0,r-46)\), or the enlarged second start \(\max(98,r-46)\). The blocker-interior condition keeps these starts in the displayed ranges. The two enlarged intervals remain disjoint. This argument concerns the specified aligned two-block family.

For all 630 parts, independently reconstructed retained vertices, initial forbidden vertices, iterative degree pruning, anchor components, size/parity requirements, and fixed crossing counts. Replayed each saved degree-deletion order and checked its final stability. Every replacement requires 47 vertices, with 24 of its starting parity and 23 of the other parity. Results agree exactly: 106 `STATIC_EXCLUDED`, 209 `PENDING`. All 315 baseline records are unchanged except the intended `PENDING` to `OPEN` status conversion. No smaller-width exclusion is transferred upward.

## Upper/lower decomposition and actual ports

Independently enumerated upper arms breadth by length, checking distinctness and all nonconsecutive adjacencies. The finite enumeration visited 13,919 prefixes across 222 distinct cached inputs. Reconstructed every upper-arm pairing, lower domain, lower endpoint, length, and cross-part exclusion. All 3,535 configurations match the saved data, including their assignment to contexts.

Exactly 185 contexts have the unique crossing allocation required by this decomposition: 20 with allocation \((0,1)\), 13 with \((0,2)\), 100 with \((1,1)\), and 52 with \((1,2)\). With crossings equal to the number of upper anchors, each replacement contains one lower segment and at most one upper arm at each end. All other allocations remain outside the reduction. The 24 unsupported context IDs are 34–42, 79–87, and 124–129; their saved alternatives match independent parity and face-capacity calculations.

The revised mask exempts a lower endpoint from upper projections only when an upper arm actually attaches there. Verified for every original configuration that each retained lower-to-upper adjacency is an intended crossing. This corrects the generic limitation recorded in round 228. Upper arms belonging to different replacements are also checked for equality and adjacency, and each lower domain excludes every projection of the other replacement's upper vertices.

No singleton lower segment occurs in either saved configuration set. Minimum original lower lengths are 40 edges for the first segment and 13 for the second. The source nevertheless preserves the zero-edge case: coincident endpoints are required exactly when the length is zero; the selected-vertex model then selects one vertex with selected degree zero, and reconstruction returns that singleton. Two upper arms sharing its upper mate cannot survive the upper-arm disjointness check. This is source reasoning, not an executed zero-edge example.

Exact grouping gives 2,323 groups and 2,048 undominated representatives before the boundary restriction. Every recorded domination has identical ordered endpoints and lengths, strict componentwise domain containment, and a terminal representative. Grouping discards upper-route distinctions only for the existential lower-pair problem; any surviving pair can be assembled with its associated upper template.

## Boundary condition and branch coverage

The width-46 cut requires at least one replacement to omit both of its old boundary neighbours. If both replacements selected an old boundary neighbour, inducedness would force that neighbour immediately next to its anchor. Trimming one unchanged edge from each replacement would give the same complete candidate in the width-45 family. A trim cannot expose either forbidden endpoint neighbour as an anchor, because that vertex cannot be selected in a valid extension to 24.

Independently checked all 978 individually available trims and all 738 pairs of available trims. Every pair maps to a context in the pinned width-45 coverage; 210 current contexts admit at least one trim on both parts. The direct model explicitly guards `a.width == 46` and `closure.width == 45`. The template preparation has the corresponding guards. The boundary condition remains conditional on the complete native width-45 exclusion.

Each of the 3,535 templates is split into both boundary choices before grouping. A chosen old boundary neighbour already present in fixed upper vertices or mandatory lower anchors rejects that branch. Otherwise the chosen old neighbours are removed from the corresponding lower domain. Closed neighbourhoods of the other part's mandatory anchors are removed, followed by necessary degree, component, size, and parity pruning.

Independent reconstruction of all branch records, parent maps, and resulting literal domains agrees exactly:

| Branch result | Count |
|---|---:|
| Fixed boundary neighbour | 5,866 |
| First lower part disconnected | 272 |
| Second lower part disconnected | 46 |
| Prepared | 886 |
| Total | 7,070 |

The 886 configurations form 538 exact groups and 496 undominated representatives. All recorded strict containments and terminal representatives were checked. Exactly 89 of the 185 supported contexts have no surviving template. The 24 unsupported contexts are preserved unchanged. The boundary disjunction is fully incorporated in the domains before grouping, so no residual choice is lost by task deduplication.

## Transfer and model assembly

Repeated the complete finite containment scan against prior round-228 representatives, allowing path exchange and endpoint reversal. Exactly one transfer exists: current representative 790, context 197 with intervals `[4,50]`, `[115,161]`, is contained in prior representative 593 without exchanging paths. Both have endpoint pairs `{18,225}` and `{107,244}` and lengths 44 and 40. Current domains have sizes 87 and 86; prior sizes are 88 and 89. The removed vertices are respectively `{35}` and `{35,245,247}`.

Prior representative 593 has one saved `INFEASIBLE` iteration, no cycle cuts, and a byte-matching record in round 228's `data/reduced45/result.json`. Its exported model hash is `d81d87088cff6038775ed0ddd681ab13495b96ebd406a8c7cc74011a06532ae1`. The old reduced-model source is pinned by SHA-256 `ed8c6aec38dc186ed4243fb6a1653d12acc087f9572c51ced2ad843b1b44a9d1`. The transfer preserves the two separated undirected induced-path constraints; it is a containment of literal tasks, not inheritance of an entire interval-width exclusion. The other 495 representative IDs exactly match both `task-transfer.json` and the generated worker's default list.

The worker reconstructs both upper-prefix/lower-path/upper-suffix replacements, then the full seed splice and endpoint 24. Selected counts, parity counts, anchor degrees, cross-part nonadjacency, and cycle cuts preserve connected induced-path candidates. Disconnected selected cycles are a relaxation until valid cycle-occupancy cuts remove them. A reported witness must pass the explicit 193-vertex induced-path and four-crossing assertions. Assertions must remain enabled. `COMPLETE_QUERY_BATCH` or direct-model `COMPLETE_COVERAGE` describes enumeration of requested queries; individual `UNKNOWN` or `TIME_LIMIT` results would remain unresolved.

Two inherited docstrings still mention width 45 or five tasks. These are descriptive discrepancies only; the inspected guards, data, default IDs, and constraints use the current width and task set. No source was changed by this review.

## Source and data pins

SHA-256 values at review completion:

| Relative path | SHA-256 |
|---|---|
| `scripts/prepare_round.py` | `fa4543e69bea02f43e10f4e127a515b692bfb54bc367758a06afd91131f13a1f` |
| `scripts/prepare_width.py` | `391211994dabe1770ea0db0cd0be97f461f4262736a70f294a31c35d49bdc4be` |
| `scripts/prepare_baseline.py` | `4eb2a7682e497bcccfdf2671ada30a9448af1f3e891dee7a5d0f9b0c1eb7a008` |
| `scripts/prepare_lower_pairs.py` | `8df0294ccc9f0f42561c7d445ab6fe1ab0c729ca218ff5ba102edc41da8bbdcf` |
| `scripts/prepare_boundary_pairs.py` | `881e3ce992f1ed5fcc73f90901f3d1443544efe271cbd4d4bf2356ceed26a457` |
| `scripts/transfer_tasks.py` | `23923ca3113336332a882dbc662398057a608eaaaa7e539f17908ac5d02dc9fa` |
| `scripts/joint_boundary.py` | `5b92bc0b02f60650f6bd1c482fd88868ed106101780c52392f1304088fe2b85b` |
| `scripts/prepare_pair_model.py` | `cf1188803ed8d777a8a615677e6529898e87289a7d7e52c893f370c217c754fa` |
| `scripts/pair_cp.py` | `bb0db3588567e3da64b7fd12766ff5a830a8d1a650b26bc57ad05bc5b075747b` |
| `data/preparation.json` | `7c3707760384796c4cabcd4757a541074f29b848c7c68bf22824e1fb6c508703` |
| `data/regions46.json` | `94ea1833e98f07b3f4327b2f06056847474c75dbcda1f30cb2abe7bb4bd9cca6` |
| `data/baseline46.json` | `ed67f2f17da3a7712c1ff3b4118bc17e68d708c3e5363602c1269ff383094877` |
| `data/lower-pairs.json` | `7878c8629e1507328efaec26c49a2f99d3b19fe86f10066d21c71ad6582e7dd1` |
| `data/boundary-lower-pairs.json` | `414e75c3b22b80ae436976eab72b869f837aba580fab79c93cdbec22f57993fd` |
| `data/task-transfer.json` | `bda4772fe1331a5112a29e385a5bc64e2f7c98c001349235f70b090980215036` |
| `data/coverage45.json` | `7587d552787e38de6ec877c6517b87b9a6d301bb5e500a64c42465d24a5d5eef` |

Remaining scope: current native outcomes were deliberately not inspected. The 24 unsupported contexts require separate coverage. The preparation and transferred native contradiction do not establish a global upper bound or a new snake construction, and the complete geometric-to-native traversal is not assembled in Lean here.
