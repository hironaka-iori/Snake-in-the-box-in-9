# Exact adaptive-charge encoding prototype

`adaptive_pb.py` has no SAT dependency. Tests executed locally:320 exhaustive weighted-PB truth-table cases and521 share cases, all passed. One square/one recipient contribution uses454 variables,1315 clauses and21 weighted event literals. This is a correctness prototype, not a production-size encoding, UNSAT certificate or Lean proof.

For empty square F, let R_j be its seven3-cube extensions and let O_j=R_j\F be each outer square. Define q_j=sum selected O_j, h=#j:q_j>0. A snake has no selected4-cycle, so q_j<=3. For selected x in O_j,1260 times its contribution is2520/(h*q_j). LCM of all h*q with h1..7,q1..3 divides2520; each coefficient is an integer. Nonempty F contributes zero. h=0 produces no recipient; no division by zero is performed. Summing all recipients gives exactly T+2 times the number of empty squares with h>0, hence at most T+2*s0. Thus the existing global upper inequality needs no saturation assumption; only equality with T+2*s0 would require excluding h=0.

The encoder gives exact equivalence gates for F-empty, q_j=r, h=t and each event(F-empty AND x-selected AND h=t AND q_j=r). At most one of21 events is true for the fixed recipient. It also supplies exact weighted-at-most via a memoized Boolean decision diagram, not duplicated literal weights. Its full gate definitions yield a canonical extension of each base assignment. The tests evaluate all clauses under that extension and compare against an independent Fraction formula. They do not independently solve the CNF or certify a general encoding theorem.

## Concrete project interface

Subclass wincert.Encoding, as W3Encoding does, and call super().build() first. Reuse self.var for cube vertices, self.fresh() for every new gate, and self.add(clause,kind) for tagged clauses. Adapt the prototype's CNF allocator, without allocating another one-based variable namespace. For each internal centre x, use its21 eligible absent opposite corners for alpha; each negative corner literal gets weight1260.

Enumerate each3-cube R through x (84) and its three2-faces F not containing x, for252 candidate(F,R) incidences. For each F obtain all seven extensions, not only R or visible extensions. Determine the relevant O_j containing x. Add the21 reciprocal events and their integer weights, sharing the q/h/F gates by geometrically canonical square F across every centre. Add all centre objectives into one weighted cap. Test `sum(1260*a(x)) <= T-1`; UNSAT would establish an integer window lower bound>=T, provided geometry and encoding soundness are proved. Static alpha restrictions and lazy cycle cuts remain as in milestone22/24/25.

Every vertex used to calculate the seven extension occupancies is within distance4 of x. Radius4 suffices; radius3 does not in general. Assert every required vertex belongs to self.B. Never treat invisible vertices as absent or use h_visible: that can overestimate shares and make an invalid lower-bound certificate.

Existing w3enc.totalizer is unweighted but accepts repeated literals. Repeating1260-scale weights is exact in principle but can explode. The prototype BDD is exact and unweighted-CNF compatible with CaDiCaL/LRAT, but is pseudo-polynomial in cap and may also explode. A production binary-adder/comparator or generalized totalizer is a likely better path. Such new gates need clause tags and Lean semantics; LRAT certifies contradiction of the emitted CNF, not that the CNF expresses this charge.

## Validation / formal obligations

1. Prove geometric incidence enumeration and1260*a equality, q<=3 and all required vertices in radius4. Prove the global inequality, including any undonated h=0 squares and endpoints.
2. Prove exact-count and event gate semantics, weighted objective/cap semantics, then extend LocalWindowTags/TagsSplit and packed Cnf generators. Existing alpha tags do not automatically cover this objective.
3. Preserve exact key metadata: directions, alpha bounds, objective threshold, scale1260, counted centres and radius. These are weighted-window lower bounds, not ordinary forbidden-alpha keys unless threshold is integrated into the state/edge-weight theorem.
4. Do not reuse6-symbol alpha automaton tables as if adaptive charge were alpha. Use the weighted-edge framework from milestone22, retaining full-product checking and window orientation/normalization proof. Shared charges are invariant under coordinate permutation, but recipient/face mapping must be established.
5. Reconstruct a cold static CNF from every accepted bound, including all lazy cuts and threshold assumptions as unit clauses. Run CaDiCaL LRAT, trim/replay, and check clause soundness. A warm solver UNSAT answer alone is not the final proof.
6. Before running a large survey, positive controls should fix a known bank snake selection and assert caps exact-1 and exact; the former must be UNSAT and latter SAT. Current tests only verify prototype components, not the full252-incidence objective.

No original repository file was modified; no new numerical upper bound is claimed.

