# Round 209: capacity in a two-coordinate square

The initial hypothesis was that collective restrictions on repeated visits to a retained-coordinate slice could strengthen the pairwise search. A sharper consequence comes from retaining two coordinates together. The resulting square has a unique opposite corner for each vertex. This forces a simple pattern for repeated free words, and one of the saved source's 28 coordinate pairs saturates the resulting capacity bound.

## Whole-path geometry

Write a path vertex as \((z,u)\), where \(z\in Q_2\) is its retained word and \(u\in Q_r\) is its free word, with \(r\ge1\). Divide the ordered path into maximal intervals on which \(u\) is constant. Consecutive intervals are separated by a free-coordinate edge, so their free-word parities alternate.

Consider distinct intervals of the same free-word parity. Their indices are separated by at least one interval, so vertices chosen from these two intervals are nonconsecutive. If the intervals receive the same free word, then every pair of retained vertices across them must have Hamming distance at least two. Otherwise the full vertices repeat or form a chord.

In a square, each vertex has exactly one vertex at distance at least two: its opposite corner. Fixing a retained vertex in one interval therefore forces every retained vertex of the other interval to be that opposite corner. Reversing the roles shows that both visit sets are singletons. Consequently, equal free words between distinct intervals can occur only for singleton visits at opposite corners. An interval visiting two or more square vertices must use a word different from every other interval of the same parity.

## The capacity inequality

For one free-word parity, let \(M\) count intervals visiting more than one square vertex, and let \(N_z\) count intervals whose visit set is the singleton \(\{z\}\). Select all \(M\) intervals, the larger singleton family from \(00,11\), and the larger family from \(01,10\). Their free words are pairwise distinct. There are only \(2^{r-1}\) free words of the selected parity. Hence

\[
M+\max(N_{00},N_{11})+\max(N_{01},N_{10})\le 2^{r-1}.
\]

This demand is exact for the equal-word conflicts within that parity. Give each multi-visit interval its own word. Pair as many singleton intervals as possible across each opposite-corner pair and give each pair one word; assign distinct remaining words to unpaired intervals. This uses exactly the displayed demand and respects every equal-word conflict. It does not enforce the edges and nonedges between opposite free-word parities, so it is not a sufficient construction criterion for an induced path.

The inequality is a general consequence of the whole induced path, rather than an assumption imposed on a particular branch. It applies to every valid embedding retaining the same indexed base histories.

## Saturation for the retained coordinates 0 and 5

The saved 98-edge source has 81 constant-free-word intervals for this pair. Among its even intervals,

\[
M=12,\qquad (N_{00},N_{01},N_{10},N_{11})=(5,4,10,10).
\]

Thus the demand is \(12+10+10=32\), exactly the number of even words in \(Q_6\). The 12 multi-visit intervals together with the ten singleton intervals at each of \(10\) and \(11\) use every even word exactly once.

Every remaining singleton interval at \(00\) must share its word with one of the ten singleton intervals at \(11\). Every remaining singleton at \(01\) must share its word with one of the ten at \(10\). There are nine such remaining intervals. Sharing with any other member of the selected 32 would contradict the preceding geometric restriction.

The 28-case native extraction finds no other retained-coordinate pair attaining 32 for either parity. The odd demand for this pair is 24. The numerical extraction is recorded separately from the general proof, and the capacity bound alone excludes none of the 28 cases.

## Consequences for unfinished domains

The 32 selected variables form a pairwise unequal family taking values in a fixed set of 32 words. Therefore every word occurs. A branch is impossible if a word is absent from all 32 domains. If only one of those domains contains a word, that variable is forced to take it. An outside interval's domain may also be intersected with the union of the domains of its permitted opposite-corner partners.

These deductions preserve every completion of a branch. They use the same global model and lexicographic conditions as before. They may remove a value that still has separate support in every binary relation, because those separate supports need not combine into one assignment using all 32 words.

A separate native engine implements only these required-word, unique-carrier and partner-union rules. It does not implement general matching propagation. Preparation verifies the selected clique's pairwise inequalities and every outside-versus-nonpartner inequality directly in the unchanged binary model.

The strengthened case remains open after 100 committed jobs, 2,683,356 nodes and 245.655 recorded solver seconds. Seven unfinished regions remain. The new rules record 2,253,129 unique-carrier value deletions, 10,136,052 partner-union value deletions, and 893,000 contradiction returns. These are accumulated operations across branches, not counts of distinct globally excluded assignments. No controlled comparison establishes a speed improvement.

An independent audit of all 100 saved transitions reconstructs the extended input tail and every frontier replacement. It also verifies all 22,208 equal-word table entries used to establish the clique and nonpartner inequalities. The 88 exhausted subproblems and 12 limit refinements leave seven open regions; the whole model is not excluded. This is an audit of native calculation evidence, not a Lean traversal certificate.

## Lean verification

Three modules pass with thirteen theorem dependency reports. The first checks finite-list capacity, saturation, domain-union capacity, unique support and partner support. The second checks the square's antipode property, singleton visit sets under cross-separation, and the distance reduction when free words agree. The third reconstructs the intervals from the literal 99 source vertices and checks 81 intervals, no repeated base visit within an interval, both count vectors, and the exact 32 selected even indices.

The whole-path reduction to these abstract premises has the written proof above and independent review. Its complete Lean assembly, parity-space interpretation, concrete binary model and native traversal certificate remain pending. The successful kernel calculations establish their stated components; they do not certify any complete native exclusion.

## Continuing previous work

The round 208 frontiers for retained pairs [0,4] and [3,4] were copied with their complete receipt histories and unchanged engine bytes. Their continuation retains the original constraints and coverage argument. Accepted round 208 files remain unchanged. Final totals and open/exhausted statuses are recorded in `data/completion.json`.

The continued cases [0,4] and [3,4] remain open after 150 committed jobs each, with respectively 8 and 3 unfinished regions. Their cumulative counts are 9,625,900 and 8,142,891 nodes. The independent audit verified that all 1,200 inherited run files match round 208 and that the 100 new transitions preserve the recorded states exactly.

The Q9 numerical frontier is unchanged. No new parent or global bound is obtained. A different Q8 parent would still require a separate Q9 joining argument. The goal remains active.
