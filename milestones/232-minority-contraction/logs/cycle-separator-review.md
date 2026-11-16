# Augmented-cycle separators and isometry scope

**No blocking defect found. All 33 positive separator certificates were independently verified.** The proposed extension of the combined parity-class exclusion to every cube-isometric copy of each saved seed is also valid. It follows by applying an inverse cube automorphism, without enumerating those copies.

## Separator argument

The augmented graph has the fixed 96 vertices and a distinct dummy vertex numbered 512. Its ordinary edges are the two-neighbour contraction edges; the dummy is adjacent exactly to the singleton-label ports. As established in `minority-model-review.md`, the minority construction exists exactly when this 97-vertex graph has a Hamiltonian cycle.

Deleting a nonempty set S of k vertices from a Hamiltonian cycle leaves at most k nonempty path segments. Every connected component of the remaining graph contains at least one such segment. Therefore more than k graph components after deleting S rules out the cycle. This is the appropriate cycle bound; the unrestricted-path bound would be k+1.

The implementation checks cuts of size one or two, computes the full components, and records a certificate only when their number exceeds the cut size. Treating parallel contraction labels as one simple edge does not change graph connectivity. The dummy is outside the original cube-vertex range, so its identifier cannot collide with a fixed vertex.

## Direct checks performed

The 81 certificate-file row IDs agree exactly and in order with the 81 native `INFEASIBLE` rows in `minority.json`. For each positive certificate, the audit independently reconstructed the contraction graph and ports from the fixed cube vertices using Hamming-distance-one comparisons, then added dummy 512. It verified that the cut consists of distinct graph vertices, recomputed every component, compared all saved component lists exactly, and checked the strict component-count inequality.

| Positive certificate type | Count |
|---|---:|
| Delete one vertex; two components remain | 20 |
| Delete two vertices; three components remain | 13 |
| Total | 33 |

None of the 33 recorded cuts contains the dummy. The argument would also permit a cut containing it; this observation is only a description of the saved witnesses.

Certified base IDs are:

`3, 4, 6, 7, 12, 16, 17, 19, 25, 28, 29, 30, 35, 38, 40, 44, 46, 47, 48, 50, 63, 77, 79, 104, 113, 114, 115, 117, 120, 126, 127, 131, 134`.

The other 48 rows record `NO_SMALL_SEPARATOR`; their native circuit exclusions remain the supporting evidence. Unsuccessful search loops were not repeated, so this review makes no independent exhaustion claim about possible separator witnesses. Together with the two insufficient-port and 62 unsupported-leaf cases, 97 of the 145 minority cases now have the recorded elementary explanations, while 48 retain native circuit evidence alone.

The source-graph and producer-script hashes recorded in `cycle-separators.json` match the saved bytes. The producer also reads `bases.json` without recording its hash in that file; this review explicitly pins it below and independently checked its ID/index agreement and cube contents. Its provenance was already checked in `minority-model-review.md`.

## Extension to cube-isometric seed copies

Let P be one of the saved seeds, let g be a cube isometry, and suppose a 192-edge induced candidate contains an entire parity class of g(P). Applying the inverse isometry gives a 192-edge induced path containing the corresponding entire parity class of P. Cube isometries preserve adjacency and injectivity, and preserve the two parity classes up to a common swap. For coordinate permutations and XOR translations, this follows directly from the parity of the translation word; equivalently, an automorphism of the connected bipartite cube preserves or swaps its two parts.

The inverse image contradicts the already established combined exclusion: its relevant parity class has either 96 vertices, covered by the minority case, or 97 vertices, covered by the majority case. Hence every 192-edge candidate must omit at least one vertex of each parity from every cube-isometric copy of every saved seed.

This is a symmetry transport of the existing restricted exclusion. It is not a full isometry enumeration, a claim that the saved seeds exhaust all relevant snake classes, or a global upper bound. It retains the native-evidence qualifications of the underlying majority and minority exclusions. No additional fixed-endpoint or fixed-order premise obstructs the transport, because both constructions allowed endpoints and order to vary freely.

## SHA-256 pins and limits

| File | SHA-256 |
|---|---|
| `scripts/cycle_separators.py` | `46be43f4b530a3f990bd50cf574233d4e83d0266573b3775c1f449ae2910d36a` |
| `data/cycle-separators.json` | `df949459f71695c50f1744528bc5e6c4f3b6ee41c083a16f88e93696a913096f` |
| `data/bases.json` | `ff2356155763cb4bf8f2d1eff80f893021793deca4c76e9183f990ecb6b3297b` |
| `data/minority.json` | `fd1b70411da2b277171ef84cf8a3169d67c1215290b995a123c2aeb67b2a9e48` |

Paths are relative to `milestones/232-minority-contraction`. The graph witnesses and written combinatorial arguments were checked here; their finite extraction was not checked in Lean. No solver, compiler, software test, manuscript edit, or modification of existing evidence was performed. Only this report was written.
