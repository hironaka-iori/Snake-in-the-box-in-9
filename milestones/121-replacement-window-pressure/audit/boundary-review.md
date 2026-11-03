# Independent boundary-path review

All three saved positive full-cube candidates pass independent induced-path validation. Each selected set is a single path in $Q_9$, with exactly two endpoints, no repeated vertices and no extra adjacency between nonconsecutive vertices. The reconstructed orders orient the designated six-transition window as $012032$.

| Probe | Vertices | Edges | Window start $r$ | Five exact counts | Pair |
|---|---:|---:|---:|---|---|
| `012032-full-pair26` | 143 | 142 | 120 | $(10,2,8,6,12)$ | $(2,6)$ |
| `012032-full-pair35` | 139 | 138 | 114 | $(13,3,12,5,12)$ | $(3,5)$ |
| `012032-full-pair44` | 145 | 144 | 136 | $(12,4,12,4,13)$ | $(4,4)$ |

The window vertices in each oriented order are $(0,1,3,7,6,14,10)$. The pair uses the second and fourth internal centres: indices $(122,124)$, $(116,118)$ and $(138,140)$ respectively. Every pair sums to eight. These are exact counts, including exact values above six; they are not graph bucket values.

## Independent checks

The script reconstructs adjacency directly from one-bit differences, traverses from an endpoint, reverses the order when necessary to orient the designated window, and verifies that the order contains the entire selected set. It then checks all unordered vertex pairs against the equivalence between cube adjacency and consecutive path indices. The three pair totals are 10,153, 9,591 and 10,440, giving 30,184 checks overall.

At each designated internal centre, the script removes the two used transition directions and enumerates the 21 pairs of remaining directions. It counts which corresponding distance-two vertices are absent from the complete selected set. The resulting five counts agree with both the probe records and the requested pair values. The evidence includes the actual absent vertices for each count.

The radius-nine records cover all 512 cube vertices. Their input and producer hashes were checked. The script also validates the saved cycle cuts as connected induced cycles and checks that none is wholly contained in the final path: 15 cuts for pair26, none for pair35 and 108 for pair44. The positive-path conclusion follows from the direct finite geometry checks and does not rely on a solver's negative-result status.

The oriented endpoint pairs are $(66,34)$, $(18,66)$ and $(34,66)$. Complete vertex orders and exact start indices are preserved in `data/boundary-paths.json`; no order supplied by the parent's geometry audit was used.

## Prepared Lean witnesses

The three new source modules use the existing milestone-119 witness pattern. Their namespaces are `Snake9.Boundary121.Pair26`, `Pair35` and `Pair44`. Each has a private vertex array and vertex function, a concrete `Snake` witness, and statements for distinctness, inducedness, pointwise window directions, the exact direction list, its canonical form, the two exact counts, their sum, and existential attainment.

The finite checks use ordinary `decide +kernel`; there is no `native_decide`, `sorry` or `admit`. Each source requests eight axiom reports. The sources import the existing geometry and reference interface, with no dependency on `ActualPair121`. Thus the concrete attainment witnesses can be checked independently of the pending universal pair-bound proof.

No Lean compiler was run for this review. The native path validation is complete, while all three Lean witness modules remain source-only. Once their checks and the universal pair-bound check pass, the witnesses establish sharpness of the lower bound eight for actual snakes in this local pattern. Their lengths do not establish a new longest snake or a new global upper bound.

## Pins and reproducibility

| File | SHA256 |
|---|---|
| `scripts/audit_boundary_paths.py` | `1d6611974383dc0ad44a9fff5e8d78d45cd51029ce353a5caa5784c234e1ef3d` |
| `data/boundary-paths.json` | `5c044ec9fdde3f73cb7d1d2cf008d0033d261f6a25fa59026b09ec5507d33a34` |
| `lean/Boundary26.lean` | `166371f14e318347e618b45160b44a0824cf47b7e88aa11c69ffe7730755e91d` |
| `lean/Boundary35.lean` | `f3f96bbf839613a5f833b5c79d6dde1d91e55af1a18bba79dc91e65cc4f8cb68` |
| `lean/Boundary44.lean` | `9d566450c5706a6b39b13e9b7c189794c99dba0b1fab0946b7d0d3360f15ae28` |

The audit prints a summary by default. Its output and source-generation options create new files exclusively and do not overwrite prior evidence. It uses only the Python standard library and launches no compiler or solver. Only the six owned output files were created; `ActualPair121`, `ReferenceCoverage121`, the live proof batch and previous evidence were unchanged.
