# A sharp inequality for two singleton counts

For every snake in Q9 with eight consecutive transitions

`(a,b,c,d,e,a,d,b)`

starting at position r, where the five named coordinates are distinct,

**alpha(r+2) + alpha(r+6) >= 7.**

There are no hypotheses on the other singleton counts. The constant seven is sharp over complete snakes satisfying this pattern. A verified 140-edge snake has the displayed window starting at r = 2 and the two counts (4,3).

The surrounding transitions are essential to this statement. Removing the first and last transitions gives normalized pattern `(0,1,2,3,4,2)`. A verified 146-edge snake contains that shorter pattern at r = 71 with first and fifth internal counts (3,3), refuting the analogous lower bound seven. This is a complete snake, rather than a disconnected local assignment.

## Proof and verification

Normalize the eight directions and translate the initial vertex to zero. The selected segment is `(0,1,3,7,15,31,30,22,20)`. At each of its second and sixth internal vertices, the two path directions leave 21 eligible coordinate pairs. Count an eligible pair precisely when its opposite corner is absent. Concatenating the two lists, with repeated vertices retained with their multiplicities, therefore counts the sum of the two singleton counts.

Assume the sum is at most six and restrict the snake to the union of radius-four neighborhoods of the seven internal centres. Necessary selected-degree, interior-endpoint, acyclicity, and count conditions contain an inconsistent core with 1,076 clauses and 879 variables. No dynamically added cycle cuts are required; the ordinary encoding still contains its standard short-cycle restrictions. The refutation has 594 derived clauses and 34,159 antecedent references. Its replay, the count interpretation, and the transport to arbitrary distinct coordinate labels passed Lean.

Sixteen theorem dependency audits passed with only the usual logical axioms. These include the local contradiction, arbitrary-snake inequality, both explicit witnesses, the best-constant deduction, and the failure of the shorter-window statement. The full list and source hashes are in `data/verification.json`.

Independent checks cover 55 local/full configurations and all 131 published bank snakes. Six oriented bank occurrences satisfy the pattern; their minimum pair sum is 18. The complete 140-edge witness shows that 18 cannot replace seven for arbitrary snakes under these hypotheses.

## Effect on the aggregate model

The proved restriction removes 9,496 previously admitted transitions from the six-count graph. The remaining graph has 4,551,730 transitions. Its normalized minimum cycle mean remains exactly 42/11, established by a replacement eleven-cycle and an integer potential checked on every remaining edge. The same potential as in milestone 42 still works. The graph result does not improve the global interval 191 <= a(9) <= 236; a full Lean graph-to-snake bridge also remains pending.

## Reproduction

`scripts/probe.py` relaxes the eleven original critical windows. `pairs.py` tests the resulting pair restrictions and shorter contexts. `certify.py` exports the joint-counter core and checked-replay sources. `replay.py` builds the local proof and arbitrary-coordinate theorem. `full_cube.py` searches for complete witnesses; `witnesses.py` exports and checks them and the sharpness consequences. `controls.py` independently checks geometry and bank occurrences. `graph.py` applies the new restriction and analyzes the graph. `archive.py` packs or unpacks the lossless native certificates; `verify.py` checks provenance, source-build receipts, axiom audits, and the graph certificate without running the optimizer.

The certificate generators reuse the existing pinned local support and the milestone 41 multi-centre count theorem. Their build paths and runtime versions are recorded in the scripts and receipts. Generated graph and compiled files stay under ignored `build/`; native certificate sources are stored as checked gzip archives.

## Next investigation and manuscript schedule

Test whether equality in the new pair bound forces an endpoint in a small neighborhood of the two centres. The sharp witness has an endpoint at Hamming distance two from the first charged centre; that observation alone is not an endpoint-demand theorem. A proved endpoint demand could use the global limit of two endpoints instead of only removing another finite-state cycle.

This is research round 1 of 5 after the milestone 43 paper rewrite. The manuscript is unchanged in this round. The next scheduled full revision is after round 5, milestone 48, incorporating only results proved by that checkpoint.
