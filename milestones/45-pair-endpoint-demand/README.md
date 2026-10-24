# Endpoint demand at the sharp pair boundary

For a snake with eight consecutive directions `(a,b,c,d,e,a,d,b)`, with the five named coordinates distinct, milestone 44 proves that the singleton counts at offsets two and six have sum at least seven. This round proves:

- If that sum is at most seven, an endpoint has Hamming distance exactly two from the vertex at offset two.
- If both endpoints have Hamming distance at least three from that vertex, the sum is at least eight.
- Eight is sharp under this endpoint-distance hypothesis. A complete 148-edge snake attains counts `(5,3)` and has both endpoints at distance four.
- Excluding endpoints only within distance one is insufficient: the prior 140-edge witness has sum seven and endpoint distances two and four.

These are statements about arbitrary snakes and coordinate labels, with 16 Lean dependency audits using only standard axioms. They do not improve the global upper bound 236 or provide a longer snake.

## Geometric meaning

Normalize the directions to `01234031`. The first counted vertex is 3, with path directions 1 and 2. The contradiction proof retains endpoint exclusions at 19 opposite corners: all pairs of free coordinates `{0,3,4,5,6,7,8}` except `{0,4}` and `{3,4}`. Thus the low pair sum forces an endpoint in this explicit set. The two omitted corners are unselected because they would give an extra neighbor to an internal segment vertex.

The core contains 1,046 ordinary clauses and 19 negative endpoint units, on 826 active variables. Its refutation has 733 derived clauses and 23,414 antecedent references. The endpoint-unit interpretation, ordinary clause soundness, refutation, arbitrary-coordinate transport, distance implication, and complete sharpness witness all compile. No extra dynamically generated cycle cut is needed for the exclusion; ordinary square and six-cycle restrictions remain in the encoding.

## Reproduction and limits

`scripts/archive.py --unpack` restores the losslessly archived certificates. `scripts/replay.py` builds the implication in dependency order using the recorded local support; `scripts/witness.py` checks the complete sharpness example. `scripts/verify.py` independently reconstructs every core clause and its original meaning, checks build/source agreement and all axiom receipts, and checks the saved positive local configurations and complete paths by direct geometry. Runtime and support paths are explicit in the scripts.

The replacement critical cycle from milestone 44 has sum nine at its occurrence of this direction pattern. It survives the new lower bound eight even if all its centres are assumed far from endpoints. Endpoint demand must therefore be combined with additional restrictions to raise that model's mean. The finite model remains at 42/11; no new graph optimization is claimed this round.

The latest explicit user request schedules a full manuscript revision immediately after this research round, superseding the previous five-round checkpoint for this revision. The revision is recorded separately in milestone 46.
