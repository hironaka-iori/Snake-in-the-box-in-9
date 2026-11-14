# Indexed-path bridge for square-base sharing

Read the complete accepted Square209 and IndexedCriterion206 sources. IntervalGeometry213.lean imports those modules unchanged and contains five public results with five axiom-report commands. One private ordered-pair lemma supports the argument. No compiler or software tests were run.

The path at original index i is the two Boolean coordinates of z(i), followed by values(group(i)). It satisfies IndexedCubePath at width 2+r. For every consecutive original pair i<j, the group identifier at j either equals the identifier at i or is larger by one. The source does not assume the groups themselves are injective, nor require that all natural-number group identifiers occur.

For different group identifiers with equal residue modulo two, their representatives cannot be consecutive: equality of identifiers contradicts difference, and an increment of one contradicts equal residue. The indexed path condition therefore gives Hamming distance at least two. Block additivity and equality of the free words leave only the square-base distance. Square209.far_iff_opposite then forces opposite corners. Reversing the index order uses the involutive opposite map.

The path condition also gives injectivity directly. If another index belongs to one of two sharing groups, its base corner must be opposite the representative of the other group, hence equal to its own group's representative corner. Its free word is already equal. The full path vertices coincide, and path injectivity makes the original indices equal. The sharing_group_single_index theorem applies to either sharing group by exchanging its two representatives.

Three pairwise different groups of the same identifier parity sharing one word are impossible. The first and second base corners are opposite, as are the second and third, so the first and third base corners coincide. Their common free word makes the complete vertices equal, contradicting path injectivity and their different group identifiers.

This is a direct path-level deduction under explicit grouping hypotheses. Equal parity here means equal residue of group identifiers. Identifying that residue with the normalized free-word parity for a particular interval extraction is a separate step. Likewise, a saved interval construction must still establish its consecutive-group rule and constant free-word representation. No literal table correspondence, candidate-partner list, native propagation, traversal completeness, or new global bound is claimed.

The direct contraposition shared_word_conflict accepts representative indices with different group identifiers, equal identifier parity, and nonopposite base corners. Under the same path and grouping hypotheses it concludes that their group words differ. This is the interface for a separately checked literal representative-pair catalogue.

The source introduces no new global definitions, admitted proofs, axioms, or native_decide. Compilation remains pending with the parent task.
