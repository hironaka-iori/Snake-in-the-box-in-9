# Designated-window scan and cycle ceilings

The bounded scan of milestones109–118 found110 designated probe records:60 `UNSAT_UNCERTIFIED`,29 `SAT_LOCAL_WITNESS` and21 `UNKNOWN`. No positive designated window has direction word $012304$ up to coordinate relabelling and reversal. Positive shapes are $012340,012314,012031,012310,012034,012345,012301$. In particular, $012034$ and $012304$ are different words.

The scan covered milestone110's `data/share-probes/` and `data/plain-probes/`, together with `data/probes/` in milestones111–115 and117–118. Small JSON records directly under each `data/` directory supplied no additional designated positive records. Internal subwindows were not enumerated. The complete inventory, exact paths, source hashes and oriented positive count tuples are saved in `data/independent-cycle-limits.json`. The absence of a designated witness is not evidence that the proposed inequality holds.

The pinned milestone117 graph audit contains two $012304$ suffix placements in each saved cycle. Independent checks reproduced count reversal, count slices, cycle chaining and total weights:

| Profile | Suffix edge | Orientation | Count symbols | Clipped total |
| --- | ---: | --- | --- | ---: |
| Completed | 3577415 | Reversed | $(2,6,2,4,6)$ | 20 |
| Completed | 463728 | Forward | $(2,6,2,3,6)$ | 19 |
| Conditional | 1275421 | Forward | $(2,6,4,2,6)$ | 20 |
| Conditional | 3047861 | Reversed | $(4,6,2,4,6)$ | 22 |

The corresponding offset0 occurrences are edges1719644,2941716,3047861 and992595, respectively. Both placements matter for deletion tests; only offset1 receives the stipulated suffix credit. Every affected tuple has symbol6, meaning the interval $[6,21]$. Thus the total lower bounds considered here do not delete any entire affected bucket under the existing count-interval test.

The completed cycle has18 edges and old weight8745. The conditional cycle has3 edges and old weight1488. Existing rule deficits are zero on both saved cycles. With total-deficit coefficient24, hypothetical total lower bounds give:

| Assumed total lower bound | Completed suffix deficit sum | Completed cycle ceiling | Conditional suffix deficit sum | Conditional cycle ceiling |
| ---: | ---: | --- | ---: | --- |
| 20 | 1 | $2923/6$ | 0 | $496$ |
| 21 | 3 | $2939/6$ | 1 | $504$ |
| 22 | 5 | $985/2$ | 2 | $512$ |

Even with potential range zero, exclusion of235 requires mean strictly above $111960/227$, whereas exclusion of234 requires mean strictly above $58080/113$. All entries remain below their relevant threshold. The strongest row gives zero-range comparisons $441160/1877>235$ and $137882/589>234$. Consequently, none of these three total hypotheses alone can produce either integer improvement within the fixed rule family. These are ceilings obtained from surviving cycles; no improved minimum mean, potential, actual-snake interpretation or local inequality is established by this calculation.

The later milestone119 full-cube witnesses are reviewed separately in `audit/full-witness-review.md`; they were not part of the historical scan. No solver, compiler or full graph scan was run. Only the owned review artifacts were written.

Pins:

- Milestone117 `data/graph-audit.json`: `13039f91dc62cc7f7b476364883a0f9126978da0daa563e1ebc74aedddf19fed`.
- `data/independent-cycle-limits.json`: `97cafdca91f665dda48303671d666a605f8b2198a682a029443c8905cbc7a82d`.
