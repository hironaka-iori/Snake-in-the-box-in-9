# Three-centre targets: independent mathematical audit

These are conditional implications. Neither requested three-centre threshold is assumed to have been proved by the current search. Write v for the number of selected vertices and m=v-1 for the number of snake edges.

## Definitions and the existing endpoint theorem

The project defines localAlpha as the sum of its singleton-square indicators over the 36 coordinate axis pairs, exactly the alpha used in the new charge code. See work/spectral/stronger/AggregateSingletonBound.lean and work/spectral/SquareIncidence.lean. UpperBound247.lean proves endpoint_alpha_ge_four with premises m>=1 and that the index is an endpoint. It is not an extra hypothesis in the later aggregate files: it follows from EndpointMissingConfig, SmallPairFamilies and EndpointGeometry. In particular the proof excludes at most three missing coordinate pairs by a finite pair-family dichotomy, then uses the selected-degree and two-endpoint properties of a snake.

This audit read those source arguments and definitions; it did not rerun a Lean kernel on this machine. EndpointFourWitness.lean supplies a genuine 120-edge snake attaining endpoint alpha=4. triple_bound_arithmetic.py independently parses that 121-vertex list, checks all pair adjacencies and confirms the initial endpoint alpha is exactly four. Thus a stronger endpoint constant must not be substituted without further assumptions.

Let a(x) be the adaptive empty-square charge. The established accounting gives

    sum_{x in S} a(x) = 9214 - 35v - 2U0 <= 9214 - 35v,

where U0 is the number of undominated empty squares. Let

    q(x) = 21alpha(x) + 2e2(x) + e3(x) + V(x).

The proved score inequality is q(x)<=21a(x). Both endpoints have a>=alpha>=4. The completed one-centre checked query gives q(x)>=22 for internal vertices. The latter is a computational result with a checked CNF proof and reviewed geometric bridge, not a Lean theorem.

## Why exactly two direction shapes suffice

A block of three consecutive internal centres comes with their preceding and following path vertices: five vertices and four coordinate flips. Normalize the first two flips to 0,1. The third flip cannot repeat either earlier coordinate: immediate reversal repeats a vertex, and 010 produces a distance-one chord after three steps. Thus it normalizes to 2.

The fourth flip cannot be 2 by immediate reversal, and cannot be 1 because the last vertex would be adjacent to the second window vertex. It is either 0 or a fresh coordinate, normalized to 3. Hence exactly 0120 and 0123 occur. Translation and coordinate permutation preserve the objective and every geometric premise.

As an independent finite check, triple_bound_arithmetic.py enumerates all 9^4 direction words and checks pairwise inducedness. Exactly 504 normalize to 0120 and 3,024 to 0123; no other canonical word survives.

## Disjoint triples and the exact exclusion expression

Suppose EVERY genuine three-centre window, in both shapes, has sum q>=T. Partition the v-2 internal vertices into k=floor((v-2)/3) disjoint consecutive triples plus r=(v-2) mod 3 remaining vertices. Use the one-centre bound for those r vertices. Then

    sum a >= 8 + (T*k + 22*r)/21.

Consequently a snake can exist only if

    D_T(v) := 21*(8 - 9214 + 35v) + T*floor((v-2)/3)
              +22*((v-2) mod 3) <= 0.

As v increases by one, D increases by 757 when the old remainder is 0 or 1, and by 735+T-44 when the old remainder is 2. These increments are positive for both targets below, so exclusion at the critical v excludes every larger v as well. This avoids a hidden gap at a remainder rollover.

## Target 234 edges

At v=236, there are 78 complete triples and no remainder. For T=255,

    sum a >= 8 + 78*255/21 = 955 + 1/7,
    sum a <= 9214 - 35*236 = 954.

The contradiction has margin 8/7, or scaled margin D_255(236)=24. The monotonic increments are 757 or 946. Therefore proving both shape queries UNSAT at cap=254 would establish v<=235, equivalently m<=234. T=255 is the smallest sufficient integer threshold for this disjoint-triple argument at v=236.

## Target 233 edges: improve the proposed arithmetic threshold

At v=235, there are 77 complete triples and two remaining internal vertices. T=267 already suffices:

    sum a >= 8 + (77*267+44)/21 = 989 + 2/21,
    sum a <= 9214 - 35*235 = 989.

The scaled margin is 2, and the increments are 757 or 958. Thus both shape queries UNSAT at cap=266 would imply m<=233. The initially proposed T=268 is also sufficient but is one unit stronger than necessary; it gives margin 79/21. This correction uses the existing one-centre bound on the two leftover internal vertices.

The exact script checks every possible v through 512 and the symbolic remainder increments. Its JSON explicitly labels these implications conditional.

## Static-cycle folding audit

The source objective builder emits the unit clause -selected(z) for every z in E.forbidden. These z are the neighbors of a fixed internal centre other than its two specified path neighbors, so the clauses are necessary for every genuine snake.

A cycle clause containing such a z is already satisfied by that unit. Omitting all those cycle clauses therefore preserves the models of the formula under its existing units. The all8 manifest may retain the complete cycle list for reproducibility, while the CNF hashes and proof IDs must use only the filtered list actually emitted. research_loop.py follows this ordering: it filters before appending static cycle clauses and before calculating the CNF digest. Saved proof hints consequently refer to the correct database.

The folding does not justify deleting any other cycle, and a finite-budget UNKNOWN still proves no numerical bound. Both shape exclusions must complete with checked proofs before either target conclusion can be asserted.
