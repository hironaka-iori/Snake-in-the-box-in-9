# Harvest and lower-pair reduction review

Read the complete `harvest_boundary.py` and `prepare_lower_pairs.py` sources and independently reconstructed their saved outputs. No blocking issue was found in these two stages. This review used immutable file comparisons and finite upper-graph enumeration only. No solver, compiler or software test was run.

## Interrupted batch and retained results

The execution record remains `INTERRUPTED`, with `LOW_FREE_MEMORY` and exit code 1. Its saved result bytes, every execution source/input pin, stdout/stderr hashes and all 62 recorded model hashes match. The saved rows contain 34 terminal `INFEASIBLE` results, 27 `UNKNOWN` results and one `RUNNING` result, context 65. The overall batch is not accepted as complete.

Every carried infeasibility has one recorded terminal solver iteration, no cycle cuts and its completed row timing. These 34 rows were saved before a later query was terminated; that interruption does not change their individual recorded outcomes. Their native solver contradictions have not been independently replayed or transferred to Lean.

The baseline was reconstructed field for field from the prepared rows and the saved native results. Its 308 contexts comprise 107 original static exclusions, 34 `PARTIAL_BATCH_EXCLUDED` rows and 167 `OPEN` rows. The latter include the 27 unknowns, the interrupted context and 139 unattempted pending contexts. No unknown, running or unattempted context became an exclusion.

The accepted completed query IDs are:

`1–12, 15, 18, 33–41, 45–55`.

These native results inherit the width-44 closure premise of the audited width-45 boundary model. The harvest does not remove that qualification.

## Forced allocation and finite reduction

For each of the 167 open contexts, independently recomputed both anchor face parities, possible crossing counts within the total budget, and exclusion of zero crossings when the anchor face has fewer than 46 available vertices. A context is reduced only if exactly one allocation survives and each path's crossing count equals its number of upper anchors.

This yields exactly 154 supported contexts:

| First/second crossing allocation | Contexts |
|---|---:|
| $(0,1)$ | 16 |
| $(0,2)$ | 24 |
| $(1,1)$ | 78 |
| $(1,2)$ | 36 |

The other 13 contexts remain unsupported and open: `78–85` and `122–126`. Contexts 78–85 retain allocations $(0,2)$ and $(2,0)$; contexts 122–126 retain $(1,2)$ and $(3,0)$. They cannot be discarded by this one-lower-segment reduction.

With zero crossings and lower anchors, a path stays lower. With one crossing and opposite-face anchors, it has one lower segment and one upper segment. With two crossings and upper anchors, it has an upper prefix, one lower segment and an upper suffix. Thus the supported allocations justify the enumerated template form.

An independent breadth-by-length enumeration, checking full pairwise inducedness at each extension, reproduced all 151 distinct upper-enumeration inputs used across these contexts. Every template count and node count matches. Combining the compatible upper pieces, deleting cross-face projections, and retaining both lower anchors reproduces all 2,141 saved configurations exactly. The two reconstructed replacements each have 46 vertices. All resulting lower lengths are positive and have the correct endpoint parity. There are no unintended vertical contacts between a selected lower anchor and a nonattachment upper vertex in these concrete templates.

## Grouping and domination

The key includes both first anchors, first length and first domain, together with both second anchors, second length and second domain. Independently reconstructing the key gives exactly 1,423 groups. Every direct domination preserves all four endpoints and both lengths, includes both smaller domains in their target domains, and is strict in at least one domain. The chains are acyclic, with maximum length two. Following them reproduces the saved flattened map and leaves exactly 1,242 representatives.

A compatible lower pair for a smaller-domain task also satisfies its containing task. This supports removal for the combined existence search. It does not identify the upper pieces or preserve configuration-specific witnesses. Every eventual candidate still needs its recorded upper pieces, original intervals and complete 193-vertex pairwise audit.

These groups concern the current lower-pair problems without an additional boundary-change restriction. Any later instantiation of that restriction must use each original upper template and its original interval before regrouping; a boundary choice cannot be copied between configurations merely because their unrestricted lower tasks agree.

## Scope and subsequent stage

The reduction does not itself exclude any of the 154 supported contexts. It provides finite lower-pair tasks. Unsupported contexts remain unresolved. The earlier native harvest remains separate from this preparation, and no complete width-45 cover is claimed.

The proposed `prepare_boundary_pairs.py` stage was not yet included in this review. Its artifact and its explicit width-45 guard require a separate extension once the source is declared ready.

## Pinned evidence

- `scripts/harvest_boundary.py`: `f514adda02c6dc4ed14bea1630ba80c464aadce030453249930fd56d94be49f1`.
- `scripts/prepare_lower_pairs.py`: `718f8fd64159e5d621ae5367b16a3b07943efdf6a902a07fff664dd7fc120f92`.
- `data/baseline45.json`: `495f7b7f544c3dd22d681e7ecc03b44d5d2eae5bfb1fb776318dfb0529fc2671`.
- `data/lower-pairs.json`: `36db50e0498768de092cbb2528bf32488f1133c0f591702462bcf1ab52621a88`.
- `data/boundary45.json`: `8aa03b3ca6f75965c3e9a4fe0ef4840557160a71a6abc7ca6ededb923f824968`.
- `data/boundary45-execution.json`: `685656ef67fc250cd2d9da9a732d3e7c697512b587a652795d833f88ba8f6672`.

## Boundary-instantiated reduction and model addendum

After the new artifacts were declared ready, read all of `prepare_boundary_pairs.py` and `pair_cp.py` and independently reconstructed every boundary branch and saved reduction. This completes the subsequent-stage review marked pending above. No blocking issue was found for the current literal data.

The new preparation explicitly requires input width 45, completed native closure width 44, and matching closure pins. It splits each of the 2,141 original upper templates into two choices before any grouping: the first or second replacement must omit both of its old boundary neighbors. If an old neighbor is already a fixed upper vertex or a mandatory lower anchor of the chosen part, that branch is impossible. Otherwise it is removed from that part's lower domain. The other part's mandatory lower anchors and their neighbors are then removed from each domain, followed by necessary nonanchor degree peeling, anchor connectivity, size and parity checks.

All 4,282 branches are accounted for exactly: 3,527 fixed-boundary-neighbor contradictions, 78 first-part disconnections, five second-part disconnections, and 672 surviving branch configurations. Independently recomputing the pruning by simultaneous fixed-point deletion reproduces every surviving domain, every branch record and every parent-configuration mapping.

The boundary disjunction has therefore been instantiated in literal domains before deduplication. A solution of a retained task automatically satisfies its representative's selected branch; no omitted residual Boolean condition has to be transferred between upper templates. The resulting key gives 392 exact groups and 331 undominated representatives. Every domination preserves both endpoint pairs and lengths and is strict in at least one domain. The default worker ID list matches all 331 representatives in the saved order.

Exactly 69 of the 154 supported contexts have no remaining branch configurations. That is a conditional finite reduction using the completed native width-44 premise, not a newly replayed solver contradiction or a Lean proof. The 13 unsupported contexts are unchanged and remain unresolved.

The model now reconstructs **both** replacements as their own upper prefix, lower path, and upper suffix. The source uses each configuration's actual first endpoints and lower length, selected counts, parity, induced degrees and mutual nonadjacency; the earlier cycle-cut reasoning remains applicable. All 672 symbolic reconstructions have two 46-vertex replacements and a 193-vertex full sequence with endpoints 0 and 24. Concrete acceptance retains the complete pairwise inducedness and four-crossing audit. No current native batch outcome was inspected.

A generic template limitation is explicit: the helper exempts both lower anchors when deleting projections of its own upper vertices. In a one-upper-arm configuration, the non-crossing lower endpoint should generally be excluded if its upper mate occurs in that arm. Independent examination of all 2,141 original configurations and all 672 surviving configurations found **zero** such offending nonattachment contacts. Thus this does not invalidate the current literal tasks. Reusing the helper on wider or different data requires an explicit actual-port distinction or equivalent exclusion; no pinned source was changed during this review.

The earlier harvest and its interrupted status remain unchanged. No complete width-45 exclusion, new witness, or global bound follows from this source/reduction audit.

Additional source pins:

- `scripts\prepare_boundary_pairs.py`: `14732d5ebf78948209bd16a07dbc9d62c7aa623335fa640387347874d028e1af`
- `data\boundary-lower-pairs.json`: `2a0212a2034039b3ddddb1c6f788b6d9761fdf6cd0efbbb3c837b749ebf38503`
- `scripts\pair_cp.py`: `ed8c6aec38dc186ed4243fb6a1653d12acc087f9572c51ced2ad843b1b44a9d1`

The preceding harvest/reduction review bytes were preserved verbatim; their SHA-256 was `cc5bc59dd7320940768dbf2f85852f714045cf53df84c53971cf78aab6658fe9`.
