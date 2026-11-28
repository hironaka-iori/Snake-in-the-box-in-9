# Round 280. Rebuilding the two ends after the left tip opens

Every nine-dimensional snake containing the **first 92 edges of archive path 191-0** has at most 191 edges. The archived donor attains 191. Both tails may change in all nine dimensions. This conclusion also covers every longer prefix of the same donor. [Ordered prefixes and target decisions](decisions.json)

At retained length 127, the only possible first move at the left tip goes from vertex 0 to vertex 32. **Requiring that move gives an exact maximum of 186.** The ordered construction is in the `best` field. Its 187 vertices were checked pairwise. A checked contradiction excludes 187 edges. Any longer snake through the same 128-edge interval could be shortened at its free ends to 187 edges. [Construction and exclusion](forced-step.json)

## Certificate argument

Keep the interior of the retained interval occupied. Each interior vertex already has its two path neighbours. An outside vertex touching this interior would create a chord. An outside vertex touching both retained tips would close a cycle. Remove these unavailable vertices and retain only sites reachable from either tip through the remaining graph. The retained tips each already have one edge into the interior.

Choose the remaining sites for a target length. The two global endpoints must have degree one and all other selected vertices must have degree two, counting every cube adjacency. Count the two parity classes separately. At 192 edges the 193 path vertices split 97 to 96, and both endpoints lie in the larger class. A square contributes at most three sites and a three-cube at most five: in either face the induced subgraph is a union of paths. Checking all subsets of the respective cubes verifies these capacities.

These conditions may also admit a path together with disjoint cycles. The solver checks the actual graph of any satisfying selection and rules out a selected cycle before accepting a construction. An infeasible relaxation already excludes the corresponding snake. The saved LRAT proofs were reduced to the additions supporting their final contradictions and checked again against regenerated formulas. The audit separately reconstructs reachable sites using Hamming distances. [Encoding](interval.py) · [Geometric audit and proof digests](audit.json) · [Proofs](proofs)

For the shorter prefixes of lengths 88 and 90, the odd-endpoint case was excluded in the donor's coordinate labelling. Their even-endpoint cases remained open under the recorded allowance. Both parities remained open at lengths 72 and 80. The next round moves the interval along the same donor to determine which consecutive segments a longer snake could retain.
