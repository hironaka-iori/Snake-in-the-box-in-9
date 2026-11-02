# Next reduction: traverse the two potential trees with the acceptance diagram

Parent verification update: the smaller Boolean experiment below is now
complete. Both variants passed Lean for completed context 99/37. In the fresh
sequential pair, the decidable comparison took 61.672 seconds and direct
Boolean comparison took 92.234 seconds. No other Lean process was present at
launch; unrelated system activity was not isolated. Retain the decidable
comparison. This single pair does not establish a universal timing ordering.
The structural traversal proposal remains unimplemented and unverified.

The most credible structural reduction is one generic traversal that carries the current acceptance node, the source-potential subtree and the target-potential subtree. It should retain the existing specialized weight expression and the full code accumulator. This removes repeated descent from both potential roots at every accepted leaf. Its Lean proof and runtime benefit remain unchecked. Before implementing it, run one strictly smaller experiment using the existing direct Boolean comparison, as described below.

## Smaller first experiment: direct Boolean comparison

The inspected Lean4.19 source already implements `Nat.decLe a b` by testing `Nat.ble a b = true` and returning a `Decidable.isTrue` or `Decidable.isFalse` constructor. `Decidable.decide` then selects true or false from that constructor. `Nat.ble` itself is the underlying recursive Boolean comparison. Both `Nat.ble` and `Nat.decLe` carry the same `lean_nat_dec_le` external implementation annotation.

Thus replacing `decide (a ≤ b)` with `Nat.ble a b` changes no comparison algorithm and removes, at most, the decision-instance and Boolean-extraction wrapper during kernel reduction. The proof evidence inside the decision constructors uses theorem applications; the source does not justify claiming that a large recursive inequality proof is constructed and normalized at every leaf. Compiled execution also has the same external primitive, so an improvement there should not be presumed.

The two open expressions are not literally the same source expression. This read-only inspection does not establish that a generic equality closes by definitional reduction. Their semantic equality follows from the existing `Nat.ble_eq` theorem, which identifies `Nat.ble a b = true` with $a\leq b$, and the corresponding standard theorem for `decide`. A small checked Boolean equality is sufficient for the existing bounded transfer theorem; no new evaluator definition or traversal is necessary.

The first experiment should therefore change only the leaf comparison in one already-certified context, prove that Boolean equality, and compare under the same workload conditions. If the difference is negligible, do not multiply this experiment into isolated context lemmas. The shared potential descent below is the substantive reduction to investigate next. No timing or kernel-equivalence test was run in this task.

Local implementation evidence: `lean-4.19.0-windows/src/lean/Init/Prelude.lean`, lines913–914,1742–1747 and1908–1910; `Init/Data/Nat/Basic.lean`, line118.

## Current repeated work

The existing prefix checker shares acceptance-diagram traversal among codes with a common prefix and stops at rejecting node zero. Its leaf callback still evaluates both fixed potential trees from their roots. Milestone102 already removes the outer206-block lookup, but each accepted code can still cause two five-level calls to `Potential99.value`, including comparisons and subtractions at each level.

`PotentialTree99.Tree` supports constant leaves at any depth. Its internal constructor stores an unrestricted natural width. The current generated potential files use complete five-level trees with widths1296,216,36,6,1; the generator shares named subtrees but does not collapse constant subtrees to earlier leaves. The numerical literal audit checks these widths and reconstructs the saved arrays. That numerical check is useful source evidence, and does not itself provide a Lean premise for a new digit-based traversal.

The proposed traversal should select potential children as digits are read, sharing those selections over the subsequent acceptance subtree. No change to the existing potential literals or their representation is needed.

## Exact invariant

Write the six zero-based digits as $a_0,\ldots,a_5$, with $0\leq a_i<6$, and let

$$
c=\sum_{i=0}^{5}a_i6^{5-i}.
$$

The diagram receives symbols $a_i+1$. After $k$ symbols have been consumed, the accumulator is the base-six encoding of $a_0,\ldots,a_{k-1}$ and the acceptance node is exactly the node reached by those symbols.

The source potential depends on $c/6$, whose digits are $a_0,\ldots,a_4$. Thus its subtree has consumed the first $\min(k,5)$ of those digits. The target potential depends on $c\bmod7776$, whose digits are $a_1,\ldots,a_5$. Its subtree has consumed the first $\max(k-1,0)$ of those digits, for $0\leq k\leq6$.

For every completion of the current prefix, the invariant is that evaluating the original source root at $c/6$ equals evaluating the carried source subtree at the still-unread source suffix. The analogous equality holds between the original target root at $c\bmod7776$ and the carried target subtree at its unread suffix.

Consequently:

| Consumed digit | Source subtree | Target subtree |
|---|---|---|
| $a_0$ | Descend using $a_0$ | Leave unchanged |
| $a_1,\ldots,a_4$ | Descend using that digit | Descend using that digit |
| $a_5$ | Leave unchanged | Descend using $a_5$ |

At the end, both residual indices are zero. The accepted-leaf check is the original inequality using the two carried values at zero, with the original clipping operation retained:

$$
P+\min(R,\mathrm{value}(T,0))
\leq w(q,d,c)+\min(R,\mathrm{value}(S,0)).
$$

The completed profile uses $R=551$ and the conditional profile uses $R=602$. No assumption that clipping is redundant should be introduced.

## Width checks and constant leaves

Selecting child $j$ by a digit is sound at a node with $r>0$ unread potential digits only when its width is $6^{r-1}$. The local arithmetic statement is

$$
0\leq j<6,\quad 0\leq u<6^{r-1}
\quad\Longrightarrow\quad
\mathrm{value}(T,j6^{r-1}+u)
=\mathrm{value}(T_j,u),
$$

where $T_j$ is the corresponding child and the stored width has that required value. A constant leaf can be retained unchanged for every digit because its value ignores the index. Checking only that a width belongs to the five allowed values would be insufficient; its level must also agree.

The recommended implementation should check the required width when taking each potential step and return false if it fails. These local guards supply the shape evidence for the accepted paths inside the same checked computation. This avoids generating separate Lean declarations for the tens of thousands of named potential nodes or repeatedly proving whole-tree validity per context. At zero remaining potential digits, evaluate the residual tree at zero; this remains correct even without an additional leaf-shape assumption.

Rejecting acceptance nodes should return true before inspecting potential shapes. Accepted terminal node one must continue until all six digits have been read: the weight and potential values can still vary between completions. The original code must remain available for count-cap and conditioned-credit tests.

## One proof interface for all remaining contexts

The useful deliverable is one checker and one reusable soundness interface that concludes the existing context-check proposition, using the already-checked fixed-block and weight equations. The proof should establish the invariant above by induction, preserve the six-symbol encoding and apply the original interval characterization to accepted bounded codes. Rejected codes satisfy the edge check directly.

`contextCheck_of_bounded_prefix` cannot consume a different checker merely because the traversals appear similar: its explicit premise is the original `checkPrefix` equation. The new interface must either prove the required old-checker equation or directly reproduce its short accepted-code-to-context argument using `checkInterval_iff`. A direct adapter avoids introducing unrelated intermediate abstractions.

The same generic interface should then generate both profile certificates for every remaining saved context. Reuse the existing selected-rule, conditioned-credit, endpoint, block and potential-root equalities. Keep the pending reference-catalogue and conditional-floor premises at their existing semantic interfaces. No additional graph or weight definitions are needed.

## Verification before adopting the reduction

First check the generic proof, including width guards, early leaves, the one-digit target delay, the source stopping before the last digit, and the clipping operation. Then compare the accepted code sequence and evaluated source/target values with the current bounded leaf tests for the saved contexts. Existing numerical prefix digests can establish that the executable prototype neither loses nor adds accepted codes; they do not replace the Lean implication.

Benchmark the current and proposed checkers under comparable process and memory conditions, using at least one simple context and one context where capped history credit affects the final weight. Record source, object and log hashes. The archived runs with other workloads do not establish a controlled speedup.

If the proof and a bounded pilot succeed, generate a single resumable sequential batch for all remaining profile/context pairs, with explicit expected coverage and a final all-context assembly. Avoid extending the work into many isolated pilot lemmas. The principal gain would be sharing potential descent between codes; the specialized weight evaluation and acceptance traversal still have costs, so a speedup magnitude cannot be inferred from this analysis.

Review scope: read-only inspection of the current prefix checker, potential evaluator, literal generator and numerical literal audit, plus the fixed-block interface, context99/37 certificate source and local Lean Boolean/decidable comparison implementation. No Lean definition, compiler run, finite certificate job or source modification outside this note was performed.
