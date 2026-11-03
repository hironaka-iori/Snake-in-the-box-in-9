# Independent review of the eleven-rule graph experiment

## Result and evidence scope

The saved `middle5-outer16` experiment passes the bounded independent audit. No discrepancy was found in its saved cycles, reconstructed weights, full-key diagram membership, potential bytes, ranges or comparison arithmetic.

| Profile | Cycle length | Weight sum | Mean | Potential range | Exact comparison | Integer part |
|---|---:|---:|---:|---:|---:|---:|
| Completed local floors | 18 | 8745 | $2915/6$ | $1730/3$ | $1324108/5623$ | 235 |
| Conditional floor 18 | 3 | 1488 | $496$ | $602$ | $551765/2348$ | 234 |

The new script adapts the earlier independent cycle audit. It reconstructs the original weights and raw source/target states from the pinned direction, geometric-share, history and floor models; compares them with the original full-key graph arrays; and evaluates every saved cycle edge in the exact retained diagram. Parallel edges retain their full direction/history/count keys. The producer's restricted full-weight hashes are preserved as provenance, but those full weight vectors were not independently regenerated.

All 42 window placements on the 21 saved edges were checked against all eleven rules. The two compressed potential files were decompressed and checked against their recorded uncompressed hashes. Both contain 1,601,856 signed 64-bit entries. Their minima are zero; the completed maximum is 3460 with denominator 6, and the conditional maximum is 602 with denominator 1. Every cycle edge has zero potential slack. The edge chains close, and the displayed cycles have 18 and 3 distinct source vertices, respectively.

The script inspected the producer's all-edge verification assertions and pinned its source. It did **not** repeat the rule predicates or potential inequalities over every graph edge. Consequently the matching whole-graph lower certificates rely on the producer's recorded checks; the attaining cycles and their weights are independently verified here. No solver or Lean compiler ran.

## Rule, placement and deletion semantics

The added hypothesis is

$$
012034,\quad \alpha_{r+3}\le5
\quad\Longrightarrow\quad
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}\ge16.
$$

Its recorded probe is `UNSAT_UNCERTIFIED`, with no added cycle cuts. The review checks the identity of this probe, the other ten rule records, their bounds, selected positions and negative thresholds. It does not promote the new rule to an actual-snake theorem.

The two tested six-transition words start at offsets 2 and 3 of the nine-transition extension. Their count windows start at offsets 0 and 1 of the six-digit count code. Both placements can exclude an edge; only the latter contributes extra charge. Every rule in this experiment has reversal-symmetric bounds and selected positions, which permits comparison with the canonical shape up to reversal. Normalized reported count tuples reverse with their words.

A symbol 6 denotes the interval $[6,21]$. Applicability requires the entire represented interval to satisfy each hypothesis. Deletion from a positive sum deficit requires every participating digit to be below six. The extra charge is the maximum applicable suffix deficit, multiplied by the minimum positional coefficient on its selected positions. With the five coefficients all equal to 24, this reproduces the producer's weights on every saved edge.

The saved removal set contains 249,185 original edges, leaving 4,697,823. It contains the previous universal-22 removal set and adds **23,285** deletions. This is also the new rule's recorded marginal count. The inherited removal sets, ranges, cardinalities and these set differences were checked. This review does not independently establish that every removed edge satisfies a rule predicate.

The new removal set excludes 14 edges of the previous 26-edge completed cycle and 4 edges of the previous 6-edge conditional cycle, agreeing with the earlier target review. Thus the cycles reported here are replacements, rather than unchanged old obstructions.

## Fixed-family coefficient limit

Every applicable deficit is zero at **both** placements of every saved cycle edge. The saved bonus is therefore zero throughout both cycles. The completed weights are

$$
480,252,720,256,368,736,365,732,360,
240,732,360,720,252,360,720,372,720,
$$

and the conditional weights are $736,496,256$.

For this fixed eleven-rule family, changing the nonnegative deficit coefficients cannot change these cycle weights. The deletion predicates also do not depend on those coefficients. The cycles therefore bound the attainable minimum means above by $2915/6$ and $496$ for every permitted coefficient choice. The balanced coefficients attain these values under the producer's all-edge certificates. This is a limit on this fixed family, not on stronger local rules or a different global accounting argument.

The exact scaled comparison is

$$
\frac{1098960\cdot6+8\cdot2915+3460}{4200\cdot6+2915}
=\frac{1324108}{5623}.
$$

Even zero potential range cannot exclude length 235 at this mean, since

$$
111960\cdot6-227\cdot2915=10055>0.
$$

Similarly $116160-226\cdot496=4064>0$ prevents excluding 234 at the conditional mean. No numerical global upper-bound improvement follows from this experiment.

## Replacement windows for the next bounded test

The completed cycle uses shapes $012034,012301,012304,012310$; the conditional cycle uses only $012301,012304$. Their shared windows are listed below. All tuples here are **bucket tuples**: every occurrence of 6 denotes $[6,21]$.

| Shape | Profile | Canonical bucket tuple | Clipped total | Outer sum or clipped outer sum |
|---|---|---|---:|---:|
| $012301$ | Completed | $(4,2,6,2,3)$ | 17 | 11, exact |
| $012301$ | Conditional | $(4,2,6,4,2)$ | 18 | 12, exact |
| $012304$ | Completed | $(2,6,2,4,6)$ | 20 | 18, clipped |
| $012304$ | Completed | $(2,6,2,3,6)$ | 19 | 17, clipped |
| $012304$ | Conditional | $(2,6,4,2,6)$ | 20 | 16, clipped |
| $012304$ | Conditional | $(4,6,2,4,6)$ | 22 | 20, clipped |

For $012301$, the completed tuple occurs at edge 1719644, placement one, and edge 463728, placement zero. The conditional tuple occurs at edge 1275421, placement zero, and edge 992595, placement one. Their outer counts are exact despite the middle interval. A valid outer-sum lower bound of 13 on these windows would therefore exclude occurrences on both cycles directly. This is only a candidate suggested by the saved windows: no search for prior counterexamples, native test or proof of that inequality was performed in this assignment. Any middle-count condition must cover the full interval $[6,21]$ to delete the represented edges; replacing it by exact six would require separate excess accounting.

For $012304$, selected outer sums contain two interval symbols. A lower bound above a clipped sum could create excess credit, but cannot automatically justify deleting the entire bucket. Exact original edge indices, orientations and placements are preserved in the JSON audit.

## Reproduction and pins

`scripts/independent_graph.py` prints its JSON by default. Its optional `--output` opens a new file exclusively and refuses to overwrite existing evidence. The successful audit completed in approximately three seconds. A Git commit-graph warning was emitted while retrieving the pinned algorithm source; retrieval succeeded and its hash matched the result record.

| Artifact | SHA256 |
|---|---|
| `scripts/independent_graph.py` | `84c7197e35a9dcfdc3d7cf43207e4a849d3e65edf142841125ab4adb984d0201` |
| `data/graph-audit.json` | `13039f91dc62cc7f7b476364883a0f9126978da0daa563e1ebc74aedddf19fed` |
| `data/middle5-outer16/results.json` | `9c1dbfb8bfb5ad4f7ceed82bfb550e178febddaff699b540bd4933a7fd3dd9a0` |
| `data/middle5-outer16/removed-indices.json` | `47a30b951071923dbb1cf8c7acb3bf7bf9ebf26836dc04dbd1d88af99687f7ab` |
| `data/middle5-rules.json` | `da6f3cb15b868886b2a05bf9fa86a01b3e20611f360d840969a036023e9349e3` |
| Completed potential, uncompressed | `4494023f3fd81a874ee6ba3d45967a72e89a0bffa9615223cbfd94b457f41f5b` |
| Conditional potential, uncompressed | `941c0b548fa4a2e151d07da836a90a9b8e97ad04e4208eaa70e3a5bb2fe4b330` |

The JSON records the remaining source, probe, compressed-potential and dependency pins. The local hypotheses and missing checked graph integration remain explicit; this audit certifies the stated bounded numerical checks only.
