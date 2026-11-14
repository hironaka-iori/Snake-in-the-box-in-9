# A direct proof about the 98-edge eight-cube parent

**Problem.** The 99 indexed vertices of the seed fix the histories of two coordinates in an eight-cube. Can a different 98-edge induced path fit those histories, up to cube isometry and reversal? Such a parent would supply a new input for the nine-cube construction.

**Direct refutation.** The retained pairs **{0,6}** (Case 22) and **{0,5}** (Case 23) admit no inequivalent parent. These refutations start from the unrestricted root domains of the two pinned formulas. They cover the entire indexed-history cases and are independent of all prior native subtree counts. Each original parent still provides a valid 98-edge path. The exclusions concern the existence of an inequivalent one.

### From an arbitrary lift to a satisfying assignment

1. Write each vertex as two retained bits and six free bits. When a retained bit changes the free word stays fixed. When both retained bits stay fixed the free word changes in exactly one coordinate. The indexed seed therefore determines the runs on which the free word is constant. There are 78 runs in Case 22 and 81 in Case 23.
2. Translate the free coordinates to make the starting free word zero. Name the first free direction coordinate zero, making the second run's word one. This is possible for every fitting path and preserves both fixed histories. Run parity then determines the parity of the six-bit word.
3. For every pair of indexed vertices the full distance is the sum of the retained and free distances. Successive vertices require distance one. All other pairs require distance at least two. This gives the complete set of word-pair restrictions on the indicated domains. [Independent geometric reconstruction](parent_geometry.py) checks all 4,851 indexed pairs, every normalized variable domain and every permitted word pair against the original formulas.
4. The remaining coordinate permutations fix the first bit direction. All 120 alphabet permutations in the formula were verified to be actual six-coordinate permutations of that form. Choose the lexicographically least word assignment in the orbit; this representative satisfies every lex-leader comparison. If a path is inequivalent to the seed, all members of its orbit are inequivalent. The 120 forbidden assignments in each model have explicit full-cube isometries to the seed, which the verifier checks vertex by vertex. Therefore none of those exclusions can remove an inequivalent parent.
5. An inequivalent lift now supplies a satisfying Boolean assignment. Exactly one word is selected per run. For a lexicographic comparison with permutation p, the prefix flags may be chosen true precisely while the prefix is fixed by p. At the first unequal position the selected word is smaller than its image, so all clauses hold. A checked refutation contradicts existence of the lift.

### Proof data

[Encoder](parent_sat.py) builds the word formula from the untouched root model at commit `cfa2e8ed386259be99cd2564361591cd92a3b7bc`. CaDiCaL produces a refutation, then drat-trim checks it and writes its essential clauses. A second drat-trim run verifies the extracted proof against the full starting formula. The compressed inputs and extracted proofs use the prefix `parent-proof-CASE--1`. The numeric -1 denotes the full root. [Case 22 receipt](parent-sat-22--1-checked.json) and [Case 23 receipt](parent-sat-23--1-checked.json) identify the exact hashes. The root refutations took 729,687 and 658,789 solver conflicts respectively. The original project recorded Case 22 as open across nine native regions at round 216. [Round 216 comparison point](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/cfa2e8ed386259be99cd2564361591cd92a3b7bc/handoff/CURRENT_STATUS.md).

To reproduce a geometric check run `python parent_geometry.py 22`. To recreate the root certificate run `python parent_sat.py 22 -1 --full --budget 6000000 --checker /path/to/drat-trim` in the branch checkout on Windows with PySAT 1.9.dev17; substitute the second case number as needed. The written implication from hypercube geometry and the independently checked Boolean proofs give the stated finite exclusions. The longest known nine-cube path is unchanged by them.

### Five further checked root proofs

| Case | Retained pair | Input | Conflicts |
|---:|---|---|---:|
| 9 | 3, 4 | Saved root | 1,006,122 |
| 24 | 0, 4 | Saved root | 1,708,961 |
| 0 | 6, 7 | Generated from the seed | 232,440 |
| 3 | 4, 7 | Generated from the seed | 189,077 |
| 4 | 4, 6 | Generated from the seed | 271,113 |

All five compressed core refutations were checked against their complete starting formulas. The independently written [model generator](parent_family.py) agrees on the exact binary relation tables, normalized domains and forbidden assignment sets for all four available saved root models. For generated cases, pass `--generated` to the encoder and the geometry verifier. The original archive excluded the separate pair {1,4} in its native traversal. These seven checked root proofs plus that existing result bring the combined recorded coverage to **eight of 28**, including all four unfinished cases listed in the [round-217 handoff](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/8931c1efdf9397211b2047b7fea8e446c5d642d3/handoff/CURRENT_STATUS.md).

### Two additional cases from chronological normalization

Cases **5** and **13**, retaining **{4,5}** and **{2,4}**, also admit no inequivalent 98-edge parent. Translate the first free word to zero and name coordinates in order of their first appearance in the transitions. This can be done on every path and preserves the two retained histories. The 120 forbidden equivalent assignments reduce to one canonical word assignment in each case. This exact assignment was independently checked to occur in the original forbidden list. The distance-closure computation was also rebuilt by direct enumeration of all 64 cube words for its triangle operations. The checked formulas use both parity families of distinct words and the whole closed distance table. The generic lemmas and capacity argument are in [the distance note](DISTANCE_PROOFS.md).

CaDiCaL used 348,885 and 210,833 conflicts. The original and extracted DRAT proofs verified in each case. [Encoder](parent_firstuse.py), [certificate replay](normalize_parent_proof.py), [Case 5 receipt](parent-firstproof-5.json), [Case 13 receipt](parent-firstproof-13.json). The total is now **nine independently checked full root proofs**, plus the earlier native result for {1,4}, covering **ten of 28** retained pairs.

### Nine more full roots with chronological and lexicographic symmetry

Retained pairs {5,7} and {5,6} are cases 1 and 2 and remain separate from these nine. Cases 6, 7, 8, 10, 15, 16, 17, 21 and 27 have new checked full-root refutations. In order the retained pairs are {3,7}, {3,6}, {3,5}, {2,7}, {1,7}, {1,6}, {1,5}, {0,7}, {0,1}. This brings the combined coverage to **19 of the 28 pairs**, including 18 full-root proof files on this branch and the previous native {1,4} result.

The word variables are constrained both by the existing lexicographic comparisons and by the fact that free directions can be named in chronological order of first use. These normalizations agree. The first free direction is already fixed. At the first point where two permutations assign different labels to a newly introduced direction, all earlier used directions have the same labels. Both new bits were zero in every earlier word. The smaller label makes the new numeric word smaller. Thus the lexicographically least assignment labels the first new direction by the least unused bit, then repeats the same choice at each subsequent first occurrence. The auxiliary flags state exactly which bits have appeared by each run. Assigning their truth values from this least representative satisfies all new clauses.

Case 27 has a large extracted proof. Its ordered `.core.gz.partNN` files are separate gzip streams. Concatenate their uncompressed contents and verify the receipt's SHA-256 before replay. [Encoder](parent_sat.py), [ordered part checker](parent_core_parts.py). Each case uses its own `parent-sat-N--1-checked.json` receipt with a complete root model, both file hashes and the independent checker result.

Case 20, retaining coordinates {1,2}, was subsequently excluded at the full root after 4,977,509 conflicts. Its original and trimmed proofs both verified. This brings combined coverage to **20 of 28**. [Case 20 receipt](parent-sat-20--1-checked.json).
