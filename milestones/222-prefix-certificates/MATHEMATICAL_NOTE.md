# Round 222: complete exclusion for the saved parent

The saved 98-edge path in Q8 has no compatible 93-edge partner beginning at either endpoint. Its one-crossing Q9 constructions, including all cube-isometric copies of the parent, have at most 191 edges. The global interval remains 191 to 233. No compatible 92-edge partner was verified, so attainment of this restricted ceiling is not claimed.

The proof combines necessary path constraints, a complete prefix tree, and independently audited exact weighted inequalities. Lean checks the generic prefix and inverse-isometry arguments. The complete numerical tree and coefficient assembly have separate exact-arithmetic audits; an end-to-end Lean assembly is not claimed.

## Model and prefix argument

For the saved parent P and root t equal to 0 or 78, remove every parent vertex except t from Q8. Only these vertices are removed; their neighbours remain available. Each allowed graph has 158 vertices and 337 edges. Opposite-layer Q9 vertices are adjacent exactly when their projections agree, so a unique projected intersection at t is exactly the compatibility condition for a one-crossing join.

An actual 93-edge partner selects 94 vertices, 47 of each parity, with an even root and an unrestricted odd terminal vertex. Its vertex indicators, endpoint indicators and induced-edge products satisfy every row of the frozen round-221 long model. The independent structural challenge reconstructs all 3145 and 3110 rows from necessary degree, product, occupancy-cycle, forest and disagreement-parity constraints.

For a proper prefix of k edges, with k less than 93, every nonroot prefix vertex is selected and has free-endpoint indicator zero. This includes the last vertex of the partial prefix: injectivity prevents it from being the final vertex of the full path. The next vertex must be an allowed neighbour of the current vertex, must be unused, and must be nonadjacent to all earlier prefix vertices. The three results in Prefix222 derive these restrictions from indexed path assumptions.

Append the prefix selection and endpoint-zero equations. A certified upper bound below 94 excludes the entire branch. Otherwise enumerate every next vertex satisfying the restrictions. Every actual continuation belongs to one child. An upper bound above 94 establishes no completion.

## Complete finite coverage

| Prefix edges | Nodes | Excluded leaves | Expanded nodes |
|---:|---:|---:|---:|
| 1 | 14 | 3 | 11 |
| 2 | 33 | 23 | 10 |
| 3 | 21 | 17 | 4 |
| 4 | 9 | 8 | 1 |
| 5 | 1 | 0 | 1 |
| 6 | 2 | 2 | 0 |
| Total | 80 | 53 | 27 |

There are no pending leaves. Three exclusions are inherited from round 221; 77 new calculations give 50 further excluded leaves and 27 expanded nodes. The largest exact leaf bounds are 93.963070 at root 0 (31 leaves) and 93.984077 at root 78 (22 leaves). Both are strictly below 94.

After four edges the sole surviving prefix was (78,206,198,196,197). Its only next vertex is 213, followed by either 215 or 221. The two final exact bounds are 93.979475 and 93.414818. The independent audit reconstructs all child lists and parent relations, with no omitted or duplicate continuation.

For each certificate, multiply inequality rows by nonnegative integer weights and equality rows by signed weights. Let r be the residual after subtracting these weighted row vectors from the objective scaled by one million. Since every variable lies between zero and one, the positive residual coefficients bound the residual contribution. All 574 residual coefficients, weighted right sides and resulting rational upper bounds are recomputed independently. Numerical optimality is unnecessary.

Any proposed 93-edge partner follows its own prefix through the tree to an excluded leaf. Every expanded depth is less than 93, so the required next vertex exists. Its 94 selected vertices contradict the leaf's bound. Any longer partner has a compatible 93-edge prefix, so all partners have at most 92 edges. Adding the saved parent's 98 edges and the crossing gives at most 191.

## Symmetry and the earlier fractional limitation

An inverse cube isometry pulls a partner for an isometric parent back to a partner for the saved parent. It preserves length, injectivity, adjacency, nonadjacency, the joining endpoint and avoidance of other parent vertices. PartnerIsometry222 checks this generic implication and reports no axiom dependencies. This is standard invariance; no novelty is claimed. Different parent classes and multiple-crossing arrangements remain outside the result.

The round-221 exact fractional points of weight 94 still satisfy every occupancy-cycle, subset-forest and disagreement-cycle parity inequality. A fractional point can distribute selections across several possible prefixes and need not satisfy a definite prefix branch. Requiring actual prefix choices and excluding early final endpoints supplies information absent from those three complete continuous families.

## Verification and continuation

The first native run completed 45 queries and stopped for low free memory. Its status remains interrupted. Twenty pending prefixes were saved. A continuation completed 29 queries and left one depth-four prefix; three further queries closed it. Each completed certificate is independently checked, and every continuation ledger is reconstructed. No incomplete native result is accepted as an exclusion.

Evidence: data/prefix-audit.json, data/deep-audit.json, logs/model-validity-review.md, and the two Lean acceptance receipts. The generic modules supply four checked results. The concrete numerical assembly remains separate. No software tests were created or run.

Do not restart the unchanged 93-edge partner query for this parent or its cube-isometry class. Further construction work must use a different parent class, a shorter parent with a sufficiently long partner, or several crossings. The unfinished six-coordinate history searches and lower-dimensional multiple-component examples remain relevant. A compatible 92-edge witness would clarify sharpness within the excluded family, without improving the global lower bound. The conjectured value 196 and the independent rebuild of contributor233 remain unresolved.

After saving, compiling and publishing this substantial route-closure result, pause under the user's result-based rule. The decision is based on this investigation, independently of contributor updates. No email was sent because no email-sending connection is available.
