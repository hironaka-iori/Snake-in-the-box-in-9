# Bounded prefix transfer

Initial delegated design note. The parent subsequently compiled the generic theorem successfully; its axiom report contains only the permitted standard axioms. Concrete finite checks have separate receipts.

The module imports `PrefixChecker100` and adds one theorem, `Snake9.BoundedPrefixTransfer102.contextCheck_of_bounded_prefix`. It adds no definitions.

Its arguments, in order, are `test`, `w`, `P`, `π`, `di`, `q`, `cls` and three explicit premises:

1. The saved context maps to the specified class.
2. The depth-six prefix checker succeeds on `test` from that class's recorded root.
3. For every accepted code $c<46656$, `test c` equals the Boolean decision of

$$
P+\pi(\mathrm{edgeTarget}(q,d,c))
\leq w(q,d,c)+\pi(\mathrm{edgeSource}(q,d,c)).
$$

The conclusion is the existing `contextCheck w P π di q = true`. Weight arguments remain ordered as history, direction, code; the context-check arguments remain ordered as direction, history. No endpoint or state definition is replaced.

The proof applies the existing interval characterization to the complete range $0\leq c<46656$. Rejected codes satisfy the original edge check directly. For an accepted code, the existing `accepted_code_of_prefix_check` theorem supplies `test c = true`; the bounded equality premise transfers that result to the original inequality. Thus no equality outside the bounded code range, or on rejected codes, is required.

This interface allows potential-block lookup equations whose validity depends on the code bound. Those equations, the chosen test, the saved-context equality and the concrete successful prefix check remain explicit caller obligations. The theorem does not change the weight, potential, retained diagram or count encoding, and introduces no new actual-snake premise.

The single axiom-print command was checked by the parent. This generic theorem alone establishes no numerical certificate or upper-bound improvement.
