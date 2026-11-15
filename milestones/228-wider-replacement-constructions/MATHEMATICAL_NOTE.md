# Round 228: complete native exclusion through width 45

All 308 maximal width-45 contexts of the selected endpoint-24 construction are computationally excluded. Consequently two length-preserving replacement blocks of at most 45 edges cannot extend this fixed seed to a 192-edge snake with four coordinate-8 crossings. This is a restricted construction exclusion. No new witness or global upper bound is obtained, and the maintained interval remains \(191\le a(9)\le233\), with the independent rebuild of the contributor's completed upper-bound assembly still pending.

## Construction family and interval coverage

The source is the normalized bank-123 induced path with 191 edges, endpoints 0 and 88, and four coordinate-8 crossings. The proposed construction retains each block's original anchors and every original position outside its open interior, replaces each block by a path of the same edge length, and appends vertex 24 after vertex 88. Its target has 193 vertices and 192 edges.

The source vertices adjacent to 24 occur exactly at indices 7, 143 and 191. Index 191 is the intended attachment at 88; the blockers at indices 7 and 143 must lie in the two changed interiors. The maximal intervals are

\[
[a,a+45],\quad a=0,\ldots,6,
\qquad
[c,c+45],\quad c=99,\ldots,142.
\]

There are \(7\cdot44=308\) pairs. Every shorter admissible pair can be padded by unchanged original positions into this grid. For an interval ending at index \(r\), the choices \(a=\max(0,r-45)\) and \(c=\max(99,r-45)\), respectively, provide containing intervals. The blocker and length conditions put these choices in the stated ranges. The first padded interval ends by 51 and the second begins no earlier than 99, so they remain separated. Padding preserves the complete candidate and its four crossings.

The prepared domains remove retained nonanchor vertices, their forbidden neighbours, vertex 24 and its forbidden neighbours. Each block's own anchors are restored. Repeated deletion of nonanchor vertices of degree below two and restriction to the anchor component preserve every actual replacement. A 45-edge path requires 46 vertices, with 23 of each parity. These necessary conditions exclude 107 contexts geometrically. The independent preparation review reconstructed all 616 initial and final part domains. Preparation itself imports no smaller-width exclusion.

## The conditional boundary restriction

The later models use the completed native width-44 exclusion for this same seed, endpoint and crossing count. At least one width-45 replacement must omit both original vertices immediately beside its anchors.

Indeed, if an old boundary neighbour is selected in an induced replacement, its adjacency to the anchor forces it to occupy the adjacent path position. That unchanged edge can be removed from the replacement interval, leaving the same complete candidate represented by a 44-edge replacement. If neither block omits both boundary neighbours, one such trim exists in each block. Both trims preserve the blockers in the open interiors: exposing a blocker as a retained anchor would select a vertex adjacent to the appended endpoint 24. They also preserve the total crossing count, even when a trimmed crossing moves into the unchanged portion. The resulting two width-44 replacements contradict the preceding native exclusion.

This argument is a conditional use of that complete width-44 result. It supplies no Lean contradiction certificate for the preceding numerical cover. It also does not justify applying the same cut at arbitrary larger widths: one trim at width \(w\) leaves width \(w-1\), so the relevant preceding-width exclusion must be supplied separately.

## Saved rows from the interrupted initial batch

The initial boundary batch ended with LOW_FREE_MEMORY, exit code 1 and overall status INTERRUPTED. Its immutable saved result contains 34 terminal INFEASIBLE rows, 27 UNKNOWN rows and one RUNNING row. The 34 completed results were retained individually; the interrupted batch was never treated as complete. Their query IDs are 1–12, 15, 18, 33–41 and 45–55. Each has a terminal solver iteration and no cycle cuts, with matching source, input and model hashes in the independent harvest review.

After retaining these rows, the baseline contains 107 static exclusions, 34 completed native exclusions and 167 open contexts. Unknown, running and unattempted contexts remain in that open set until separately resolved. The 34 saved exclusions retain the native width-44 premise of their boundary model.

## Reduction to lower-dimensional path pairs

Coordinate-crossing parity is fixed by the endpoint faces. A same-face path with too few available vertices in that face cannot have zero crossings. These conditions give a unique supported allocation in 154 of the 167 open contexts:

| First and second crossing counts | Contexts |
|---|---:|
| \((0,1)\) | 16 |
| \((0,2)\) | 24 |
| \((1,1)\) | 78 |
| \((1,2)\) | 36 |

Each supported replacement has one contiguous lower-face segment. Zero crossings keep the path lower; one crossing gives a lower segment and one upper arm; two crossings between upper anchors give an upper prefix, a lower segment and an upper suffix. If the upper pieces contain \(h\) vertices altogether, the lower path has \(45-h\) edges. Upper arms may be singletons, and enumeration continues beyond a possible crossing port so that later ports remain available.

Fixing the upper pieces leaves two induced-path tasks in \(Q_8\), with prescribed endpoints, lengths and domains. Same-face pieces in different blocks must be disjoint and nonadjacent. Across faces, adjacency means equality of lower projections. Each lower path therefore avoids every projection of the other block's upper pieces, and avoids its own upper projections except at its actual crossing ports. The two lower paths must also be disjoint and nonadjacent. Together with the prepared retained-vertex restrictions, these are the conditions needed by the existing one-crossing, two-crossing and simultaneous-replacement constructors.

Independent finite enumeration reproduced all 2,141 original upper configurations. The boundary disjunction was then imposed separately on each configuration before grouping: either the first block or the second must omit both of its old boundary neighbours. A fixed upper vertex or mandatory lower anchor at an omitted neighbour makes that branch impossible; otherwise the required omissions are placed directly in that block's lower domain. Necessary degree, connectivity and parity reductions follow.

The 4,282 branches divide into 3,527 fixed-boundary contradictions, 78 first-part disconnections, five second-part disconnections and 672 surviving configurations. The survivors form 392 exact lower-task groups and 331 undominated representatives. Task equality includes both endpoint pairs, both lengths and both domains. Domain containment is used only with these endpoints and lengths fixed. The boundary choice is already instantiated in the literal domains before this comparison, so no additional template-dependent condition is lost by grouping.

Exactly 69 supported contexts have no surviving branch. The other 85 are covered by the 331 representative tasks. The first reduced batch returned 321 INFEASIBLE and ten UNKNOWN results. The longer retry addressed exactly those ten task IDs and returned INFEASIBLE for all ten. Thus all 331 unique tasks are excluded. Both batches have accepted execution receipts, exit code zero and no external stop. Each recorded solve uses the initial model with no added cycle cuts.

The selected-vertex models impose exact size and colour counts, endpoint degree one, other selected degrees two, and cross-path separation. Disconnected cycles are permitted by this relaxation. Every intended pair is included, so native infeasibility excludes the intended paths. The solver contradictions have no Lean certificates.

## The thirteen remaining contexts and complete cover

The lower-segment reduction deliberately leaves contexts 78–85 and 122–126 outside its supported class. The first eight retain allocations \((0,2)\) and \((2,0)\); the other five retain \((1,2)\) and \((3,0)\). Direct width-45 boundary queries cover these alternatives without discarding either allocation. All thirteen terminate INFEASIBLE, with an accepted execution receipt, exit code zero, no external stop and no cycle cuts.

The four disjoint context classes are therefore

| Evidence route | Contexts |
|---|---:|
| Original geometric exclusions | 107 |
| Saved terminal rows from the interrupted initial batch | 34 |
| Complete lower-pair reduction, including 69 contexts with no surviving branch | 154 |
| Direct queries for unsupported allocations | 13 |
| Total | 308 |

The saved IDs in these classes are disjoint and their union is exactly 0 through 307. The count 154 includes 69 finite branch exclusions and 85 contexts covered by the 331 unique reduced tasks. It does not represent 154 separate solver contradictions. Combined with interval padding, this completes the native exclusion for the stated two-block family through width 45.

## Projection-mask limitation and verification scope

The current general template helper exempts both lower endpoints when deleting projections of its own upper pieces. For a single upper arm, only one endpoint is an actual crossing port; the fixed lower endpoint must remain subject to projection exclusion. Independent inspection found zero offending nonattachment contacts among both the 2,141 original configurations and the 672 surviving configurations. The literal width-45 tasks are therefore unaffected. More generally, the permissive mask enlarges a lower task, which preserves an infeasibility implication but does not by itself justify reconstructing a satisfying pair. Before reuse on wider or different inputs, the helper must distinguish actual crossing ports explicitly. The pinned worker sources were preserved.

`AllocationFacts228` has an accepted PASS receipt with three axiom reports. `row_count` checks that the literal allocation table has 154 rows; `all_allocations` checks its finite allocation predicates; `forced_allocation` derives each listed allocation from the stated total, parity and zero-count permissions. The first two reports use no axioms, and the third reports only `propext` and `Quot.sound`.

These kernel checks concern allocation arithmetic. Extraction of endpoint faces and zero-count permissions from the graph data remains native. The actual-path parity and face-capacity implications, preservation by domain preparation, upper enumeration, boundary-case mapping and all solver contradictions remain separate obligations with the recorded source reviews and native evidence. This note does not claim an end-to-end Lean proof of the 308-context exclusion.

This note was prepared from the immutable source, review logs and terminal receipts. Their input pins and result links were compared, and the final context partition was checked from saved IDs. No compiler, solver or software test was run for this note. The earlier derivation note describes the stage before boundary instantiation; the completed calculation described here includes that later restriction before deduplication.

The completed result concerns only normalized bank 123, appended endpoint 24, retained anchors and outside positions, two length-preserving blocks of at most 45 edges, and four coordinate-8 crossings. Wider blocks, other endpoints or seeds, more replacement blocks and length-changing constructions remain outside this exclusion. Any new search must prepare and justify its changed family, including the correct preceding-width premise and exact projection masks.

## Evidence pins

- Prepared domains, `data/regions45.json`: `e64a1de95fe6354ec64e8a5bfc51457bafc262f581df1188a1683978c26d5bb9`.
- Native width-44 premise, `data/coverage44.json`: `f02bfee405ddc56db3923d246ea245c035f9fa19bb6132923524d46ff64e01a5`.
- Boundary-instantiated tasks, `data/boundary-lower-pairs.json`: `2a0212a2034039b3ddddb1c6f788b6d9761fdf6cd0efbbb3c837b749ebf38503`.
- Initial reduced results, `data/reduced45/result.json`: `85bdc37fef64c62b213d9a82b10e6cf8ff86b0618dee308a678057f09ed74e0e`.
- Longer retries, `data/reduced45-long/result.json`: `3589e7a379d85e110e1c6ec1e933b1e793d205aae2f2a36b3f8d04971a3a94d7`.
- Direct remaining results, `data/complex45.json`: `6607b5ebc61d955360b28e69f24497d375e49ec989717178c7f40f00cd956227`.
- Accepted Lean source, `lean/AllocationFacts228.lean`: `222619ea91ecedcc83b0a510eab2e8200233500e601680714c91b8909f7e1a8a`.
- Accepted Lean audit, `data/AllocationFacts228-audit.json`: `c9d424a51282cafbd63cbc3f7358f7cd77fbd211ff805ff1eb0049b797762446`.
