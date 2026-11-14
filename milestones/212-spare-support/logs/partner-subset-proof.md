# Partner-subset capacity

PartnerSubset212.lean imports SupportBridge212 and proposes one theorem with one axiom-report command. No compiler or software tests were run.

Let C be the chosen-family identifiers, O the outside identifiers, and J a subset of O with distinct assigned words. The chosen and outside assigned-word lists are also distinct and fit in the alphabet pool. Every actual word fits its current variable domain.

The partner-completeness premise says that whenever an outside variable and a member of C share an actual word, that member of C belongs to the outside variable's allowed-partner list. N must contain every such allowed partner of a J member whose current domains intersect. N may safely include additional candidates.

The proof uses the actual exception list E from SupportBridge212: the members of O whose assigned words are absent from C's words. Its length is at most pool.length minus C.length.

For each member of J, either its word is absent from C and its identifier belongs to E, or it shares with a chosen variable c. In the latter case partner completeness lists c as a partner, and the actual shared word witnesses the intersection of the two domains. Hence c belongs to N. Therefore

\[
\{\text{assigned words of }J\}
\subseteq
\{\text{assigned words of }N\}
\cup
\{\text{assigned words of }E\}.
\]

Capacity209.distinct_length_le applied to the concatenated lists gives
\[
|J|\le |N|+|E|\le |N|+
  \bigl(|\mathrm{pool}|-|C|\bigr).
\]

The Lean statement counts list lengths. J must have distinct assigned words, so repeated variable identifiers in J are excluded. N need not be duplicate-free for the implication, but a duplicate-free enumeration is required to interpret its length as the candidate set's cardinality and obtain the intended strength. Distinct assigned words in C and containment in the pool ensure that the displayed spare capacity is a nonnegative ordinary difference.

For no supported partners, N is empty and the theorem reduces to the bound on forced exceptions. It also applies when several outside variables compete for a small nonempty candidate set. The statement proves a necessary condition only; neither domain intersection nor satisfaction of this inequality supplies a compatible complete assignment.

The geometric conflict and partner relations, literal source interpretation, candidate-list extraction, and native pruning or traversal remain separate. No new definitions, admitted proofs, axioms, native_decide, search result, or global bound are introduced. Compilation remains pending with the parent task.
