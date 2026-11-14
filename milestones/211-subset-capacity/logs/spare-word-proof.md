# Spare words and outside singleton intervals

Spare211.lean imports the unchanged accepted Capacity209 module. Its main proposed theorem appends the distinct clique words to the distinct outside words absent from that clique. The append is duplicate-free and lies in the same pool, so distinct_length_le gives

\[
|C|+|\{w\in O:w\notin C\}|\le |\mathrm{pool}|.
\]

The two additional arithmetic consequences give at most one absent word when the clique size is 31 and at most two when it is 30, for a 32-word pool. The file has three axiom-report commands. It introduces no definitions, admitted proofs, new axioms, or native_decide. No compiler or tests were run; compilation remains pending.

## Why the outside intervals have distinct words

Fix one parity and choose the family C to contain every multi-visit interval and all singleton intervals at the larger corner family from each opposite pair of the retained square. Choose one side of a tie, not both. Every interval outside C is a singleton at one of the two unchosen corners. Those corners belong to different opposite pairs and are adjacent.

Distinct intervals of this parity have no consecutive original indices. Two outside intervals at the same corner cannot share a free word, because that would repeat a full vertex. Two at the two different outside corners cannot share a free word, because those corners are adjacent and would produce a chord. Thus the entire outside list has distinct assigned words.

If an outside interval shares a word with C, the square geometry forces its partner to be a singleton at the opposite corner. It cannot share with a multi-visit interval or with a singleton at another corner. Distinctness within C makes this partner unique in any fixed completed assignment; the partner is not prescribed in advance.

For clique size 32-s, the main inequality therefore implies that at most s outside intervals can avoid all clique words. At least |O|-s, when this is positive, must share with opposite-corner clique partners. This is a bound across a completed assignment. It does not by itself select which intervals must share or justify removing all unpartnered words from each individual outside domain.

## Counts from the saved census

Input: milestones/209-slice-capacity/data/square-capacity.json, SHA-256 400753eef4c691333e5e03d87239d93fe63ea9f7fc870ac1d742a01afb21bb10. Counts below are directly from the corresponding records.

| Retained pair | Parity | Multi intervals | Singleton counts at 00,01,10,11 | Clique size | Outside intervals | Spare words | Minimum outside intervals sharing with C |
|---|---|---:|---|---:|---:|---:|---:|
| (4,7) | even | 19 | 7,1,5,1 | 31 | 2 | 1 | 1 |
| (4,7) | odd | 7 | 9,4,8,4 | 24 | 8 | 8 | 0 |
| (0,6) | even | 12 | 5,4,9,9 | 30 | 9 | 2 | 7 |
| (0,6) | odd | 9 | 8,9,6,7 | 26 | 13 | 6 | 7 |

For (4,7), the selected singleton corners are 00 and 10 in both parities; outside corners are 01 and 11. For (0,6), the even selected corners are 11 and 10, leaving 00 and 01 outside. The odd selected corners are 00 and 01, leaving 11 and 10 outside. Each outside corner pair is adjacent, as required.

The Lean source proves only the generic finite-list and arithmetic implications. The square argument above is written reasoning using the established same-parity interval geometry; the literal census-to-list connection and any native pruning implementation remain separate. No search result, runtime improvement, novelty, or global-bound claim is made.
