# Concrete support bridge for retained coordinates (0,6)

ConcreteSupport213.lean imports ConcreteGeometry213 and introduces the six-bit decoding word(u). It reuses the imported literal source, recomputed groups, base corners, required-pair list, certificate validity, and certificate coverage. No existing source was edited, and no compilation or software tests were run.

The premise is an actual IndexedCubePath of width 8 on 99 indices, with vertex i equal to the two literal retained bits followed by the six decoded bits of values(group(i)). Values are raw natural numbers.

The consecutive_groups theorem lifts the checked Boolean calculation over the 98 adjacent index pairs to the consecutive-group premise of IntervalGeometry213. For every required pair (x,y), certificate coverage supplies representative indices i,j. Certificate validity gives the two index bounds, group identities, distinct group identifiers, equal identifier parity, and nonopposite retained corners. IntervalGeometry213.shared_word_conflict then gives unequal decoded words. Equal raw natural numbers would have equal decoded words by congruence, so the raw values are unequal.

The remaining deductions use the definition of the required-pair list:

- All unordered distinct pairs within each chosen and outside list occur in its withinPairs component.
- The four literal identifier lists are duplicate-free, established by small kernel-decided goals in this source.
- The resulting pair inequalities imply duplicate-free assigned-word lists.
- Every outside-to-chosen nonpartner pair occurs in familyPairs. If its actual raw words were equal, that required inequality would be contradicted. Thus any actual sharer belongs to the listed partners.

The two exported family results supply chosen-word distinctness, outside-word distinctness, and actual-sharing partner completeness for both even and odd index families. They match the corresponding hypotheses of the earlier Nat-valued support and exception-capacity APIs.

No upper bound on the raw values is needed for these inequality implications: raw equality always implies equality of the decoded six bits. In contrast, applying a 32-word parity capacity still requires the appropriate raw alphabet membership and parity premise. Those facts are not supplied here merely by six-bit decoding. Current domain membership and partner-domain support containment also remain premises of the subsequent filtering theorem.

This closes the stated source-specific pair-certificate interpretation subject to successful compilation. It does not claim that an arbitrary native assignment reconstructs a path, prove a complete geometry/model equivalence, identify native mask contents, or certify propagation or traversal. Four axiom-report commands are included; compilation remains with the parent task.
