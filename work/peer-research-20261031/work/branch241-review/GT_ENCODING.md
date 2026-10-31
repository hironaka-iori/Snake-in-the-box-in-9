# Forward generalized totalizer prototype

Status: implemented and checked on small exhaustive controls and real window encodings. No large SAT search was run with this encoding, and no speedup or new upper bound is claimed.

## Interface and witness integration

Construct GeneralizedTotalizer(C, terms, cap), then append the unit clause [G.target]. Each term is an existing signed literal and a nonnegative integer coefficient. C must provide one, nv, fresh() and clauses. The existing unit [C.one] fixes the true constant.

The constructor does not append anything to BinaryCNF.gates. To extend a base witness, first call the existing BinaryCNF.witness or github_query.bank_witness, then call G.extend(base_assignment). This explicitly fills every fresh GT threshold variable. It does not rely on BinaryCNF treating an unknown gate type correctly.

The root target is an asserted feasibility constraint, NOT a fully equivalent Boolean gate that can be negated arbitrarily. The property proved below is

    input satisfies weighted sum <= cap
      iff there exists an auxiliary assignment satisfying all GT clauses and [target].

The forward threshold variables are not unique. test_gt_pb.py explicitly exhibits two different legal auxiliary assignments at the same all-false input. Therefore the encoder must not be described as a collection of equivalence gates.

emit=False is a cost-estimation mode only: it reserves variable IDs and counts clauses but does not emit the actual encoding. It cannot be used as a SAT query, and extend refuses to construct a witness in that mode. Actual costs below were measured with emit=True and all clauses materialized.

## Exact normalization

Combine repeated literal coefficients. Remove the false constant, subtract the true-constant contribution from the cap and normalize complementary literals using

    A*x+B*(not x) = min(A,B) + (A-min(A,B))*x
                                      +(B-min(A,B))*(not x).

This is an identity for every input, even when different input literals are themselves outputs of correlated geometry gates. All remaining coefficients are positive. A negative residual cap gives the false target; a cap at least the sum of residual coefficients gives the true target.

Let K=cap+1. Replace any residual leaf weight w by min(w,K). Because all weights are nonnegative, clipping preserves the cap predicate.

## Merge clauses

Each leaf has one positive threshold represented directly by its existing literal. For two child threshold maps A and B, the parent has a fresh variable for every positive threshold in A, in B, or obtained as min(a+b,K).

Emit the forward implications

    A[a] -> parent[a],
    B[b] -> parent[b],
    A[a] AND B[b] -> parent[min(a+b,K)].

A pair involving child overflow K is redundant: its unary overflow implication already suffices, so it is omitted. Build a balanced tree and forbid the root overflow threshold K.

## Soundness: overflow is forced in every extension

Induct on the tree. If a subtree's actual clipped input sum is positive, its corresponding threshold exists and is forced. This is immediate at a true leaf. At a merge, either exactly one child has a positive sum, so a unary clause forces the corresponding parent threshold, or both do, so the pair clause forces their clipped sum. If a child has already overflowed, its unary K implication forces parent overflow. Thus an input sum above the cap forces the root overflow in every satisfying extension and contradicts [target].

## Completeness: canonical extension

For each node, calculate its actual clipped subtree sum. Assign each fresh output variable for threshold s to the truth value [sum>=s]. Every unary implication is valid because the parent count is at least the child count. Every pair implication is valid because the two subtrees contain disjoint term positions, and their nonnegative counts add. If the input satisfies the cap, the root K output is false. Hence this explicit extension satisfies all clauses and [target].

Soundness and completeness together prove exact projected SAT semantics for the asserted threshold. They do not prove reverse implications or uniqueness of outputs.

## Verification

- 1,736 complete input assignments: canonical extensions satisfy every gate clause, cap predicates match exact arithmetic and every above-cap fixed input contradicts by independent unit propagation.
- Signed literals, repeated literals, complementary literals, zero coefficients and true/false constants are included.
- Four malformed-input tests are rejected.
- A two-extension example explicitly checks that output nonuniqueness is retained rather than accidentally asserted away.
- Both actual three-centre direction shapes were instantiated with the original GitHub geometric Encoding. A genuine bank snake was translated/permuted into each window. The canonical extension fills all variables and satisfies all base geometry and forward PB clauses. Exact scores 669 and 566 correctly fail cap 254.

## Actual three-centre costs at cap 254

| Shape | Binary PB extra vars/clauses | GT extra vars/clauses | Whole binary clauses with static8 | Whole GT clauses with static8 |
|---|---:|---:|---:|---:|
| 0120 | 6074 / 28309 | 15897 / 611137 | 173531 | 756359 |
| 0123 | 6050 / 28197 | 15900 / 611712 | 173106 | 756621 |

The GT formulas have about 4.36 times as many total clauses. Stronger propagation may compensate, but this must be measured in actual checked searches. The current prototype is not automatically a performance improvement.

Reproduce with test_gt_pb.py and gt_cost_comparison.py. The latter builds queries and canonical controls only; it never invokes a SAT solver.

## Bounded standalone search experiments

After the cost audit, gt_probe.py instantiated each actual three-centre cap-254 query with the same filtered static eight-cycle constraints. Its temporary BinaryCNF.leq_binary override is restored immediately after construction; neither the original binary builder nor the binary checkpoints is modified. It runs at most ten solve seconds per shape, sequentially.

Both probes ended UNKNOWN. For 0120, 1,859 new RUP steps and 119,259 hints passed; total measured wall time including build, solver initialization, checking and checkpoint saving was 15.915 seconds. For 0123, 1,318 steps and 81,513 hints passed; total wall time was 15.994 seconds. Neither probe produced a SAT model or an empty clause.

GT_probes contains the exact CNFs, learned proofs, hashes and result metadata. The real bank controls satisfy all pre-target clauses with complete canonical extensions; their actual scores 669 and 566 exceed the tested cap, so they are deliberately not described as satisfying models of the asserted cap-254 queries.

These are fresh ten-second GT probes. The binary runs accumulated many longer slices and retained learning. The unequal samples support no relative speed conclusion.
