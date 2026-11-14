# Round 208: continuing exact history searches

The working hypothesis is that freeing six coordinate histories of the saved 98-edge Q8 path may produce a different parent for a Q9 construction. Round 207 excludes every choice of five free histories at the native-enumeration evidence level. Its first six-coordinate searches reached their limits. This round continues selected six-coordinate models without discarding their completed branches.

## The mathematical search space

Retain two coordinate histories at every index of the saved path. The other six coordinates are arbitrary, subject to the exact whole-path pair conditions: consecutive vertices have Hamming distance one, and distinct nonconsecutive indices have distance at least two. Consecutive steps in retained coordinates force the free word to remain constant. Merging those steps gives one free word per resulting interval. Every original pair constraint is retained, including constraints whose two indices lie in the same interval.

Translate the first free word to zero and permute coordinates so the first free transition is in coordinate zero. The residual 120 coordinate permutations act on the entire interval tuple. Retain the lexicographically least tuple in each orbit, using the previously proved fixed-prefix deletion rule. Explicit source-isometric tuples are excluded. The global acceptable-assignment predicate, including these lex inequalities, remains unchanged throughout continuation. A restricted domain region need not be invariant under the permutation group.

## Why a saved frontier is sufficient

Suppose the current region has domains \(D_1,\ldots,D_m\), and the selected variable is \(j\). For any \(a\in D_j\), its assignments split into two disjoint regions obtained by replacing \(D_j\) with \(\{a\}\) and \(D_j\setminus\{a\}\). This remains an exact split after intersecting both regions with the same acceptable-assignment predicate.

After sound propagation, depth-first search explores the first region. If that search stops, save its unfinished descendants. At every ancestor, also save the region for all values of its selected variable that have not yet been explored. Previously exhausted children contribute no acceptable assignment. Induction along the interrupted recursion stack shows that the saved regions cover every unrefuted assignment in the input region. The regions are disjoint: two different regions first diverge at an ancestor's selected value versus remaining values.

The global frontier initially consists of the root region. Replacing one frontier region by a covering list preserves coverage; soundly exhausting a region permits its removal. Consequently, an empty frontier excludes acceptable assignments, provided that every propagation and exhaustion step has the stated soundness. An empty list by itself supplies no such justification.

Lean checks the domain split, disjointness, region replacement, removal under an exhaustion premise, and empty-frontier consequence. The accepted module has six theorem dependency reports. It does not check the concrete native traversal, generated pair tables, normalization, filesystem state, or any of the numerical exclusions.

## Implementation and evidence

At a limit, the native solver copies the current domains and each unexplored sibling region before unwinding. The saved regions are independent copies. The wrapper retains the old authoritative job until the solver has returned, the result has been recorded, and the complete replacement state is ready. One atomic replacement commits the whole new state. An interrupted or rejected result leaves the old job intact.

Each transition records the source, executable and model hashes; the input and output hashes; the old and new states; and resource observations. These records identify the calculation and make interrupted progress reusable. They do not establish compiler correctness or provide a Lean certificate of the native computation.

The written coverage argument, implementation, and completed case 18 receipt chain received independent review. For case 18, all 51 linked transitions agree with an independently reconstructed state update. There are six limit refinements and 45 exhausted regions, with no unlinked receipt. The final state is exactly the last recorded after-state and has no pending region. The audit found no missing returned region or hash-link inconsistency; it does not independently establish the soundness of each native exhaustion.

## First six-coordinate exclusion

Case 18 fixes coordinates 1 and 4, using zero-based coordinates in the saved input. It has 52 interval variables. The search exhausts after 51 committed jobs and 1,713,998 nodes, with 41.908 seconds of recorded solver time. Therefore, at the native-enumeration evidence level, every induced 98-edge path retaining those two indexed histories is cube-isometric to the saved source.

The conclusion concerns these two particular histories, the saved source, unchanged length, and unchanged index matching. It does not strengthen the general requirement of six changed histories to seven: the other retained-coordinate pairs have not all been excluded. It supplies no global Q9 length bound and no new Q8 or Q9 witness.

Cases 24 and 9 retain coordinates [0,4] and [3,4], respectively. Their terminal round snapshot and continuation totals are recorded in `data/completion.json`. Any open frontier remains unresolved; neither elapsed work nor a smaller pending list implies an exclusion. The other 25 retained-coordinate pairs have only their round 207 initial limited searches.

Both continued cases have 100 committed steps. Case 24 retains five unfinished regions after 3,430,077 nodes; case 9 retains six after 3,177,434 nodes. An independent audit of all 200 linked transitions found consistent pins, input/output hashes, and complete state replacements, with no orphan receipts. Both complete models remain open.

## Limitations and next mathematical step

Continue the two saved open frontiers and then the remaining coordinate pairs. Freeze this round's accepted bytes before publication; later work should copy the unchanged engine, input, and complete case directories into a new milestone. The engine computes its milestone root from its location, and its byte hashes must remain equal to the saved pins. A changed engine requires a separately justified transfer of the mathematical frontier.

If a different parent is found, establish every pair condition, inequivalence to the source, and its endpoint data before attempting a Q9 join. A different Q8 parent alone does not construct a longer Q9 snake. If all 28 six-coordinate choices exhaust, the indexed source-specific requirement rises to seven changed histories, still with native evidence unless the complete calculation is certified.

The recorded implementation assumes a single continuation writer. It supports process-interruption recovery; complete power-loss durability is not established. A manually created per-job STOP marker checkpoints that job and does not promise cancellation of the entire batch. Resource-triggered stopping is handled by the wrapper and ends its batch after recording a complete frontier. No software tests were created or run.

The Q9 numerical frontier is unchanged: the 191-edge construction is retained; the archived 235 argument awaits its independent rebuild; the 233/234 comparisons remain conditional; and 196 remains unresolved. The contributor branch was refreshed without merging it and remains at `997f188fc2ca893b4738081943a9f6f32cb11a23`.

The goal remains active under the user's instruction to continue until she requests a stop.
