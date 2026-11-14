# Extending subset capacity to unsaturated families

This is a written next-step analysis. No matching search, implementation, Lean compilation, solver, or tests were run.

Inputs read:

- milestones/211-subset-capacity/lean/Subset211.lean, SHA-256 51f8fad00d2a807edcd9a768e1751dac0f0f85eb8241808bf0a3a8d91943ce39.
- milestones/209-slice-capacity/data/square-capacity.json, SHA-256 400753eef4c691333e5e03d87239d93fe63ea9f7fc870ac1d742a01afb21bb10. All 28 records' parity counts were extracted directly. The full interval and partner lists were not re-audited.

## Matching condition and proof

Take one recorded family of intervals whose words must be pairwise distinct. Let its current domains lie in the 32 words of the appropriate parity. A matching covering every family variable assigns each variable one distinct allowed word. It is only a necessary relaxation of the complete snake model.

Starting with a nonempty set of variables, repeatedly include every word in each reached variable's domain and, for each reached matched word, its owner variable. Let U be the resulting variable set and W its reached words. All current domains of U are contained in W. Every variable in U has its matched word in W; every matched word in W has its owner in U. Therefore

\[
|W|-|U|=\#\{\text{unmatched words in }W\}.
\]

Consequently this reached set is tight exactly when no unmatched word is reachable. In that case |W| = |U|, and Subset211.saturated_subset_covers applies to U and W. Any variable outside U that is forced to differ from every member of U can lose all W from its domain without losing a completion. For another member of the original pairwise-conflicting family, this conflict condition is automatic. For an interval outside that family, it must be established from the actual conflict relation.

If an unmatched word is reachable, this particular closure is not tight; applying the saturation removal to it is unsound. This does not rule out a smaller tight subset elsewhere. A domain union smaller than its variable subset contradicts a completion by deficient_pool_impossible, independently of whether the whole family is saturated.

Thus the existing proof applies unchanged to unsaturated families. What changes is the extraction of a genuine tight subset from the current domains. A matching that covers all variables must first exist. Failure of an incomplete matching attempt does not certify deficiency; a complete matching procedure or an explicit deficient subset is needed.

## Dummy-variable alternative

For a family of k <= 32 variables, add 32-k auxiliary variables, each with all 32 parity words as its domain, and require distinctness throughout the augmented family. Every original injection extends by assigning the unused words bijectively to the auxiliary variables. Conversely, restriction of any augmented assignment gives an original injection. This is an existentially equivalent balancing of the distinctness constraint.

A reached tight subset containing only real variables gives the same sound pruning rule. A subset containing an auxiliary variable with its full domain necessarily reaches all 32 words; its saturation does not show that the real variables use all those words. In particular, an actual interval outside the original family is not known to conflict with auxiliary variables. Applying outside_not_mem_pool to such an interval and an auxiliary-containing subset would lack its conflict hypothesis. Direct unmatched-word handling avoids this additional interpretation and is the simpler next extension.

## Capacity counts across all 28 retained pairs

Each entry is the saved demand
\[
M+\max(N_{00},N_{11})+\max(N_{01},N_{10})
\]
for the recorded parity family. Capacity is 32 for every entry. The spare-word columns are 32 minus the corresponding demand; they describe this static family size, not the size of a currently restricted domain union.

| Retained pair | Even demand | Odd demand | Even spare words | Odd spare words |
|---|---:|---:|---:|---:|
| (6,7) | 24 | 29 | 8 | 3 |
| (5,7) | 28 | 23 | 4 | 9 |
| (5,6) | 27 | 26 | 5 | 6 |
| (4,7) | 31 | 24 | 1 | 8 |
| (4,6) | 27 | 28 | 5 | 4 |
| (4,5) | 29 | 28 | 3 | 4 |
| (3,7) | 26 | 27 | 6 | 5 |
| (3,6) | 27 | 27 | 5 | 5 |
| (3,5) | 27 | 25 | 5 | 7 |
| (3,4) | 18 | 28 | 14 | 4 |
| (2,7) | 23 | 28 | 9 | 4 |
| (2,6) | 27 | 25 | 5 | 7 |
| (2,5) | 25 | 28 | 7 | 4 |
| (2,4) | 26 | 28 | 6 | 4 |
| (2,3) | 27 | 26 | 5 | 6 |
| (1,7) | 27 | 28 | 5 | 4 |
| (1,6) | 25 | 26 | 7 | 6 |
| (1,5) | 28 | 26 | 4 | 6 |
| (1,4) | 24 | 24 | 8 | 8 |
| (1,3) | 28 | 20 | 4 | 12 |
| (1,2) | 28 | 25 | 4 | 7 |
| (0,7) | 28 | 28 | 4 | 4 |
| (0,6) | 30 | 26 | 2 | 6 |
| (0,5) | 32 | 24 | 0 | 8 |
| (0,4) | 27 | 18 | 5 | 14 |
| (0,3) | 28 | 28 | 4 | 4 |
| (0,2) | 29 | 27 | 3 | 5 |
| (0,1) | 27 | 20 | 5 | 12 |

Exactly one of the 56 recorded parity families is initially saturated: even parity for retained pair (0,5). The other 55 have between 1 and 14 spare words. None exceeds capacity. The nearest unsaturated families are even parity for (4,7), with one spare word, and (0,6), with two. Their proximity to saturation is a reason to inspect current domain restrictions, not evidence that a useful tight subset exists or that either search will improve.

For the already active open pairs, the demands are (27,18) for (0,4), (18,28) for (3,4), and (32,24) for (0,5). Hence the method can also examine odd parity within the current (0,5) model, provided unmatched words are handled correctly. These counts do not exclude any model, establish runtime improvement, or strengthen a global snake bound.
