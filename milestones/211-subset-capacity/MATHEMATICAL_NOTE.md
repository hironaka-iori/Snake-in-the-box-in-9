# Round 211: subset capacity and forced sharing

The working hypothesis was that joint distinct-word constraints remove combinations that survive separate binary supports. The new native engine records active subset pruning, but no controlled comparison establishes a speed improvement. The six-coordinate case retaining [0,5] remains open. No new Q9 construction or global upper bound is claimed.

## The proved deductions

If a subset J of variables must receive distinct words, and U is the union of their allowed words, every completion gives an injection J into U. Thus |U| < |J| is impossible. Equality means all U is used within J; every other variable known unequal to every member of J must avoid U. Removing those words preserves the same complete assignment and all its other constraints.

The 32-variable family for retained coordinates [0,5] is saturated. A matching discovers tight subsets through reachability: direct an arc from a variable to the matched owner of each allowed word. A reached set is closed, so its domain union is precisely its matched words. The implementation recomputes the actual union and cardinality before every rejection or deletion. Matching failure without a genuine deficient subset is an execution error, not an exclusion. Only other clique variables are pruned; outside singleton intervals retain their possible partner sharing. This is an application of standard matching methods, not a novelty claim. The primary precedent inspected is Jean-Charles Regin, AAAI-94, https://cdn.aaai.org/AAAI/1994/AAAI94-055.pdf (abstract and matching characterization).

## A further whole-path consequence

For one parity, choose all multi-visit intervals and the larger singleton family from each antipodal pair of the retained-coordinate square. All outside intervals then lie at at most two adjacent corners. Their words must also be pairwise distinct: equal words would repeat a vertex or create a chord. If C and O are the assigned word sets of the chosen and outside families, both fit in 32 words. Therefore

\[
|C|+|O\setminus C|\le32,\qquad |C\cap O|\ge|C|+|O|-32.
\]

At most the unused capacity of C can be occupied by outside intervals without a partner in C. Every shared word must have an antipodal singleton partner, by the square geometry.

| Retained pair | Parity | Chosen intervals | Outside intervals | Minimum partner sharing |
|---|---|---:|---:|---:|
| [4,7] | Even | 31 | 2 | 1 |
| [0,6] | Even | 30 | 9 | 7 |
| [0,6] | Odd | 26 | 13 | 7 |

These are aggregate requirements and do not identify particular partners or particular outside intervals that must share. In particular, one cannot remove all unpartnered values from every outside interval when spare words remain. If several outside intervals have no possible partner support, they consume that limited spare capacity. Developing this aggregate constraint is the next useful search step.

The alternate reachability description handles unsaturated matching families directly: reached words minus reached variables equals the number of reachable unmatched words. Only closures with no reachable unmatched word are tight. The detailed written argument and all 56 parity-family capacity counts are in logs/unsaturated-extension.md. This extension is not yet implemented.

## Verification and search scope

Six new Lean modules pass with nineteen theorem dependency reports. Subset211 checks four subset-capacity implications. Spare211 and Sharing211 check unused capacity and forced sharing. Three concrete modules derive the selected even/odd counts directly from the literal 99 source vertices. Their accepted sources, objects and dependency receipts are preserved. The generic counting implications and literal extraction do not themselves assemble the complete arbitrary-path/model interpretation or certify the native traversal. The whole-path link has the written geometric proof above. The failed first Sharing211 compilation and its corrected successful receipt are both retained.

The native source review found no unsound subset rule under the inherited clique assumptions. The fixed transfer audit verifies all 606 inherited files, all seven domain vectors, their order and model pins. The transfer changes only engine pins and adds its explicit record. No frozen round-209 evidence is modified.

The new search accepted 196 transitions: 170 exhausted subtrees and 26 limited runs, adding 1,038,016 nodes and 115.378 solver seconds. It records 5,022,135 subset value removals and 84,079 subset contradiction returns. These count repeated operations across branches, not distinct globally excluded assignments. The complete model remains OPEN with eleven pending regions; totals including the old engine are 296 jobs, 3,721,372 nodes and 361.033 solver seconds.

The last job exited normally after LOW_FREE_MEMORY was recorded and retained nine new regions; two older regions were unchanged. Its elapsed time also met the ordinary job limit, so the exact internal stopping condition is not inferred. The independent saved-record audit reconstructs every new state transition and final byte sequence. It does not replace a Lean traversal certificate.

The earlier open [0,4] and [3,4] cases remain at their round-209 states. Only [1,4] is excluded among all 28 six-history choices; twenty-seven remain unresolved. The general source-specific requirement remains six changed histories at the same length and fixed index matching.

## Publication and continuation

The main paper and short explanation are updated in place, preserving authors and local hyperlink settings, with exact repository mirrors. The contributor branch advanced to c999e9bd at its 13:03 UTC report: 3125/3127 built, leaving S012301A35344 and T012304A35346K47. The former was retried after a kernel reduction failure and the latter after stack overflow; the report supplies no completed 233 assembly. This progress was inspected, not merged or independently rebuilt. The archived 235 theorem and conditional 233/234 status are unchanged.

The goal is ACTIVE after the user's explicit resume. Continue from the frozen round-211 [0,5] state, or implement the spare-capacity constraints for [0,6] in a new milestone with its own model and proof boundary. Search and proof checks retain the existing resource limits. No software tests were created or run.

Both final editor documents compiled successfully after one stale-input retry each. Source mirrors, author declarations, hyperlink settings, labels and citations are verified in data/document-verification.json.
