# Round 240 structural-note review

Status: PASS_WRITTEN_ARGUMENT_REVIEW. No mathematical correction is required in the reviewed version.

Source: `milestones/240-five-count-recovery/STRUCTURAL_NOTE.md`, all 159 lines, read completely. SHA256: `6fb2b6efca446baea64144ae6b8b78f98ee36b95898ff92dc4f8be6cd8c5cb2f`.

## Main deductions

**Generator relation and coordinate reduction.** For g_i=J+e_i, a sum over a set I is (|I| mod 2)J plus its coordinate indicator. Hence the only nonempty zero relation uses all nine generators. An odd closed walk leaves a nonempty odd relation after cancelling paired occurrences, so its length is at least nine. Taking each generator once gives a simple nine-cycle because an earlier collision would give a proper relation. A non-bipartite graph on at most eight vertices would contain an odd simple cycle of length at most seven, which is impossible.

For a connected distance-eight subgraph on k≤8 vertices, its spanning-tree labels form a set I with |I|≤7. Every translated vertex lies in their span, and independence gives unique binary coordinates. An extra edge carrying a label outside I would yield a nonempty relation involving at most eight generators. For a label in I, independence makes that edge precisely a one-coordinate difference. This establishes the claimed induced-cube embedding. Summing t distinct generators gives original Hamming weight t for even t and 9−t for odd t. The qualification on disconnected components is essential: their even cross-component coefficients generally remain nonzero.

**Eight-point matrix and Walsh classification.** The displayed vertex order is the binary-subset order of g_0,g_1,g_2. The coefficients at generator distances 0,1,2,3 are 128,35,−16,−10. Their Walsh eigenvalues are 175,189,99,−15, as stated. The vector χ is the weight-three character, so the oversized solution has the claimed signs and amplitude 21.

For any integral solution Hw=315s with ternary s, each Walsh sum S has absolute value at most eight. A weight-two equation reduces to 11W=35S, forcing S=0. All character sums agree modulo two, so S_0 is even; its equation 5W_0=9S_0 and the bound force S_0=0. Weight-one equations imply 3 divides S. Walsh inversion then reduces to 8s(x)=S_χχ(x) modulo three. Since multiplication by eight is invertible modulo three and −1,0,1 are distinct residues, one fixed a in {−1,0,1} gives s=aχ at every vertex. Every eigenvalue is nonzero, so w=−21aχ. The bound |w|≤9 leaves only zero. No implicit boundedness assumption on w is needed until this final step.

**Entire-support star.** For r≥2, subtracting two leaf equations gives 16(y−z)=35(t−u). The difference t−u is between −2 and 2, so divisibility by sixteen forces equality of both right sides and leaf unknowns. The r=1 case has a single leaf and needs no subtraction. The remaining two-by-two determinant is 18432−3273r. For r=1,…,7, its reduced absolute divisors are exactly 5053,566,957,356,689,134,1493. The numerator 128t−35s belongs to {0,±35,±93,±128,±163}; none of its nonzero values is divisible by these divisors. Thus s=t=0 and the nonzero determinant gives x=y=0. The statement correctly requires the entire support to be this star; adding other components introduces omitted coupling terms.

**Tensor counterexamples.** The Q_2 function supported at the two opposite corners has zero neighbour sum. The cube adjacency operator on a Cartesian product is the sum of the factor operators, so the tensor product is again annihilated. Extending by zero to one new face transfers that tensor product to the other face under the neighbour sum. Its support is 2^r. The stated Q_3 and Q_5 examples therefore refute the blanket dimension-sized minimum, while the Q_9 instance has support sixteen and leaves the minimum-nine conjecture undecided.

## Small arithmetic inspected

The four Walsh eigenvalues and all seven star determinants, gcd values and reduced divisors were recomputed by scalar integer arithmetic. No combinatorial search or heavy enumeration was performed.

## Prior-source check

The [author manuscript of Cores of Cubelike Graphs](https://backend.orbit.dtu.dk/ws/files/256075181/1808.02051.pdf), Section 2, printed page 7, explicitly defines the folded cube of order n by n generators with one relation and gives odd girth n for odd n. The bibliographic metadata identifies European Journal of Combinatorics 87 (2020), 103092. This supports the note's attribution; no novelty claim is needed.

## Scope

This review validates the written deductions and their stated limitations. It does not certify the finite Lean file, inspect a compiler receipt, prove universal six-through-eight recovery, or connect the matrix classification to a whole-cube Lean theorem. No source was edited, and no compiler, solver or test suite was run. The note's distinctions between an oversized arithmetic witness, a bounded matrix exclusion, a binary-selection counterexample and an actual snake construction are correct.
