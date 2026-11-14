# Six necessary changed checks on both sides of the entry-87 near walk

Start from the 193-vertex, one-chord walk obtained by inserting coordinate 4 after vertex 190 in source 87. It is row 118 in the zero-based one-chord census. For either parity side S, the 192-edge target must select exactly as many anchors as S, 97 on the even side and 96 on the odd. Any successful repair, even with unrestricted order and an arbitrary opposite class, must change **at least six** of the odd-neighbour checks of that side.

Introduce a Boolean variable at each opposite-parity address to indicate whether the check changes, and require at most four true variables. By the [inversion lemma](SYNDROME.md), the final status of an anchor v is its old status toggled once for each adjacent changed check. This specifies every anchor exactly. Select the rest of the cube freely. Require the selected induced graph to have two endpoints and degree two at every other vertex. The endpoints are anchors for the 97-member class and members of the opposite parity for the 96-member class.

With no dynamic clauses beyond the starting formula, both models are UNSAT. The independent checked resolution cores use 73,874,702 and 27,388,391 resolution steps for the even and odd anchors. Finally, the parity of the number of syndrome changes equals the parity of the number of changed anchors. Replacing one set by another of equal cardinality changes an even number of anchors. A distance of five is therefore impossible as well. Six follows.

[Formula and geometry](target_surgery.py), [even receipt](target-surgery-118-0-4-checked.json), [odd receipt](target-surgery-118-1-4-checked.json), [archived-proof replay](budgeted_drat.py).
