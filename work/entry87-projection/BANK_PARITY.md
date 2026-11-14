# An obstruction shared by all 180 one-chord candidates

Every saved 191-edge snake yields candidate walks when an extra coordinate flip is inserted. Exactly 180 indexed insertions give 193 distinct vertices and a single unwanted edge. Write E and O for their sets of 97 even and 96 odd vertices, respectively. The origin convention makes the two endpoints even.

**Theorem.** For each of these 180 candidates, every 192-edge snake with even endpoints omits at least three members of E and at least three members of O. The statement allows arbitrary vertex order, arbitrary coordinate histories and arbitrary replacement of the entire opposite class. The exclusion also transports under cube isometries, with the parity labels exchanged under an odd translation.

Use the [parity reconstruction lemma](PARITY_SETS.md) on the selected class. Of the 360 labelled input classes, 100 distinct even sets and 86 distinct odd sets occur. Duplicate sets give precisely the same reconstruction problem. Testing each distinct input and then replacing any one member by any new vertex of the same parity gives

* 100 × 97 × 159 = 1,542,300 even replacements.
* 86 × 96 × 160 = 1,320,960 odd replacements.

Within each trial the other parity remains completely free. Of 2,863,260 trials, 1,570 satisfy the elementary degree and endpoint conditions, and 1,556 of these also give a connected graph. Forced degree-two edges and proper cycles exclude 1,467 of those graphs. The other 89 have small binary proofs. There are 16 more such proofs for unchanged sets. Together the 105 proof trees contain 597 nodes, and the largest has 11. Each split includes or omits one edge of a putative Hamilton cycle. Each leaf forces a wrong degree or a closed proper subcycle. A second implementation reconstructs incidence by literal Hamming distances and replays the trees with set operations.

The previous counts exclude zero or one replacement. The two-replacement census extends the earlier entry-87 result to all 180 candidates. Across their 186 distinct input sides it searches 10,836,676,800 indexed removal/addition trials. Exactly 10,594 pass the degree filter, and 10,442 also satisfy connectivity. Degree propagation excludes 5,777, forced proper subcycles exclude 4,435, and 230 require a binary proof. Together with the sixteen unchanged-set trees, 246 complete proof trees contain 3,336 nodes. The largest has 131. Their independent replay rebuilds the entire anchor–witness incidence from distances. Repeated resulting sets across different starting sides are counted as distinct trials.

[Source candidates](bank-pivots.json), [bank survey](bank_parity.py), [native enumeration](two_parity.cpp), [complete census](bank-parity-1-0-180.json), [proof trees](bank-parity-1-0-180-trees.json), [tree generator](bank_parity_proofs.py), [independent tree checker](check_bank_trees.py).

[Two-replacement census](bank-parity-2-0-180.json), [two-replacement proof trees](bank-parity-2-0-180-trees.json).
