# Separator certificate review

**No blocking defect found. All 45 recorded separator certificates were independently verified against the saved contraction graphs.** The first file certifies 34 graphs, and the endpoint file certifies 11 distinct additional graphs. The remaining four graphs still rely on the previously audited native Hamiltonian-query results. The candidate family remains the majority-colour family specified in `contraction-model-review.md`.

## Soundness

For a Hamiltonian path, deletion of a set S of k vertices leaves at most k+1 nonempty path segments. Every component of the graph after deletion must contain at least one segment, because the original path visits every vertex. Consequently, more than k+1 components excludes a Hamiltonian path. This justifies every certificate from `cut_certificates.py`.

If the graph has exactly two simple-degree-one vertices, both must be the endpoints of any Hamiltonian path. If e of those endpoints are deleted, the number of remaining nonempty path segments is at most k+1-e. This justifies the `ENDPOINT_RUN_BUDGET` condition in `endpoint_separators.py`, although no saved successful certificate uses that condition.

The other endpoint condition is also sound. Suppose S is nonempty, both forced endpoints lie outside S, and deletion leaves exactly k+1 graph components. If both endpoints belong to the same component, that component contains the first and last surviving path segments. Those segments are distinct because S is nonempty. Every other component needs a segment as well, so at least k+2 segments would be required, contradicting the k+1 bound. All 11 additional certificates use this condition.

The proposed three-region criterion in `leaf_components.py` is valid: a nonempty region separated from the rest of the graph by one outside attachment vertex must contain a Hamiltonian-path endpoint. Otherwise a spanning path would have to enter and leave through the same attachment, repeating it. Three pairwise disjoint such regions would require three endpoints. The script obtains its regions as components after deleting an articulation vertex, so each has the required attachment property. No successful three-region certificate is recorded here.

## Direct certificate verification

The audit rebuilt simple adjacency from each survivor's labelled edges, checked cuts are distinct vertices in the graph, recomputed every connected component after deleting each recorded cut, and compared the full sorted component lists. It also recomputed degree-one vertices for all endpoint certificates and the four remaining cases. These are direct checks of saved certificates; the unsuccessful search loops were not rerun.

| Certificate source | Input graphs | Verified exclusions | Details |
|---|---:|---:|---|
| `cut-certificates.json` | 49 | 34 | Five one-vertex cuts give three components; 29 two-vertex cuts give four components. |
| `endpoint-separators.json` | 15 | 11 | Nine two-vertex cuts give three components; two one-vertex cuts give two components. Both forced endpoints are outside the cut and in one component. |
| `leaf-components.json` | 4 | 0 | No additional certificate recorded. |

The 11 endpoint-certificate IDs are `14, 1317, 1919, 5728, 6065, 6403, 10056, 16600, 20108, 22284, 22917`. Each lies outside the first 34 certified IDs. The input order and exact remaining-ID sets match at both stages, so there is no duplicated or omitted case in the handoff between these files.

The four remaining IDs and their independently reconstructed sole graph leaves are:

| Case ID | Sole degree-one vertex |
|---:|---:|
| 21881 | 312 |
| 22201 | 120 |
| 22514 | 288 |
| 22834 | 96 |

Thus the two-forced-endpoints rule does not apply directly to these four. Their `NO_THREE_LEAF_REGIONS` records mean that this search produced no additional certificate; this review does not claim that every possible separator or other elementary obstruction has been exhausted.

## Source and data integrity

Each result's source-graph and producer-script hashes agree with the current saved bytes. The endpoint file's additional predecessor hash agrees with `cut-certificates.json`. The leaf file does not record predecessor hashes, but its exact four-ID input set was independently matched to the complement of the first two files' verified exclusions. No new execution receipt or Lean verification is inferred from the presence of these JSON files.

| File | SHA-256 |
|---|---|
| `data/colour-survey.json` | `5e7ee3e1e685f4715538d155f9d095e303c75f5de48270faead094bd2f569d9d` |
| `scripts/cut_certificates.py` | `b1437c309814f89f23eac6ad31d533fd5c8fa943587faf1ef028f209cbbffc4f` |
| `data/cut-certificates.json` | `264003809485876a98dca600b9c33f6d45c2a2cab4f25aba82140196fc91d99d` |
| `scripts/endpoint_separators.py` | `0fcabd57a897bb4d7836591f487e4b49ca89343ae9846b3c43d8e3555fa67610` |
| `data/endpoint-separators.json` | `d679d94774846a9138a9493a80b2a36bf0ec3d8acc40c5149a5ffd4347995238` |
| `scripts/leaf_components.py` | `925812fed948333008b6fed1f01ff9e9ae4a6e7ca6bbcfea525e7f900bb545d6` |
| `data/leaf-components.json` | `7ebda70b53fec56b09fb0aaa53d13b8eb06815b310e504a6c1a8dbe3f8107963` |

All paths are relative to `milestones/231-endpoint-exchanges`. The direct component and endpoint checks make the reasons for 45 exclusions independently inspectable without rerunning the Hamiltonian solver. They do not supply an end-to-end Lean proof of the finite extraction or the remaining four exclusions. No solver, compiler, software test, or manuscript edit was performed; only this review was written.
