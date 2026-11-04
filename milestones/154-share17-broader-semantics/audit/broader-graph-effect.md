# Broader interval effect on saved graphs

This is a read-only graph-row inventory. No Lean compiler, solver, graph rebuild, or potential search was run.

| Placement | Orientation | Source exact | Source broader | Retained exact | Retained broader |
|---|---|---:|---:|---:|---:|
| eligible_prefix | forward | 28 | 42 | 28 | 28 |
| eligible_prefix | reverse | 21 | 42 | 21 | 21 |
| eligible_prefix | both | 49 | 84 | 49 | 49 |
| suffix | forward | 39 | 78 | 39 | 39 |
| suffix | reverse | 52 | 78 | 52 | 52 |
| suffix | both | 91 | 156 | 91 | 91 |

The source graph has 4,947,008 rows; the saved milestone144 removal set retains 4,661,572.
Across both eligible placements, the broader conditions add 100 source rows and no retained rows.

The reason is exact: the retained graph requires the second-plus-fourth count sum to be at least 9. The broader bounds make that sum at most 9, so those counts must be 4 and 5. Every added broader row has a smaller pair sum and is already removed. This conclusion concerns that saved removal set and its hypotheses.

The eleven-cycle has the same two matching suffix rows, 2222339 and 2220859. The fourteen-cycle has none. Relative to the 149 profile with universal 012032 share 16, either exact or broader share 17 would increase the eleven-cycle total from 5456 to 5458, assuming the local theorem and its integration. Broadening gives no further increase on either saved cycle.

Clipping is unambiguous: stored 6 denotes the interval [6,21], while every target upper bound is at most 5. No target match can contain a clipped value.

Next, complete the local Lean proof, then recompute the all-edge potential with the stronger suffix contribution on the chosen profile. No new potential or upper bound is established by this inventory.

The adjacent JSON records every input hash and the checked array hashes.
