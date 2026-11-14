# Round 206: unrestricted changes to four coordinate histories

The initial hypothesis was that allowing arbitrary new words in four coordinates could change the saved 98-edge Q8 parent's cube-isometry class. Complete native enumeration refutes that hypothesis for this parent, its fixed length and its indexed comparison. It makes no assertion about other parents or longer Q9 snakes.

## Exact whole-path model

Write the source as \(P=((z_i,s_i))_{i=0}^{98}\), where \(z_i\) contains the fixed coordinates and \(s_i\) the coordinates allowed to change. A target has the form \(Q=((z_i,u_i))_{i=0}^{98}\). There is no requirement that a map from selected source words to target words extend to a cube isometry.

Hamming distance adds over the two coordinate blocks. Consequently the target is an induced path in the specified order precisely when every \(i<j\) satisfies

\[
d(z_i,z_j)+d(u_i,u_j)=1\quad\text{if }j=i+1,
\qquad
d(z_i,z_j)+d(u_i,u_j)\ge2\quad\text{otherwise}.
\]

The second condition excludes both repeated vertices and unwanted edges. These are conditions on the entire snake. For nonconsecutive pairs, base distance zero requires block distance at least two; base distance one requires different block words; base distance at least two imposes no restriction. For consecutive pairs, base distance one forces equal block words, and base distance zero forces block distance one.

Merge consecutive indices joined by base-coordinate edges. Each resulting chronological interval must have a constant target block word. Giving each interval one variable therefore loses no target. Substitute these variables into every indexed pair condition and intersect all conditions belonging to a given variable pair. Conditions whose two indices lie in the same interval must also be retained. Different intervals may receive the same word when their base positions permit it.

Translate the whole target block so its initial word is zero. At every interval boundary its parity changes, so interval number \(a\), starting from zero, has parity \(a\bmod2\). The saved source starts at zero. A further global block-coordinate permutation makes the first block transition use the first coordinate. These normalizations preserve every whole-path cube class. A first block transition must exist: 99 distinct vertices cannot fit in one fixed-block slice, whose size is at most 16 in the four-coordinate models and eight in the five-coordinate models.

This yields an exact finite model for normalized targets with the specified indexed base histories. Its variables range over every word of the required parity, including words unavailable to slice-isometry constructions.

## Native enumeration and its scope

All \(\binom84=70\) four-coordinate choices were examined. Each normalized model contains six saved assignments with explicit forward global-isometry witnesses. After excluding those assignments, every search exhausts. The batch uses 2,524 search nodes; search time totals 6.578 seconds and total batch time is 14.125 seconds. These measurements describe this run only.

The implementation removes a value only when it has no compatible value anywhere in a neighbouring current domain, or when all other entries of an explicitly forbidden complete tuple are forced. Branching visits every remaining value. Resource limits return `LIMIT`; they never return `EXHAUSTED`. An independent source review found no unsound constraint or exclusion. Source, input and all 70 model hashes match their saved result records. No independent search rerun was performed.

Thus the native evidence excludes a different cube-isometry class while any four coordinate histories of this source remain fixed. A change involving fewer than four free coordinates is contained in one of these models. Under the fixed length and index matching, a different class therefore requires at least five changed coordinate histories. All 420 excluded witnesses use forward order; allowing reversal gives the same conservative exclusion statement.

This conclusion is source-specific. It neither classifies all 98-edge paths nor imposes an upper bound on Q9 snake length. It also does not show that five changed histories suffice.

The five-coordinate batch attempts all \(\binom85=56\) choices, with a nominal three-second search limit each. One model exhausts: index 23, free coordinates \(\{0,2,3,5,6\}\), fixed coordinates \(\{1,4,7\}\). The other 55 reach their limits. No new witness is found. The batch's `COMPLETE` status means that every planned model was attempted. The 55 limited cases remain unresolved.

## What Lean checks

`lean/IndexedCriterion206.lean` passes the guarded Lean 4.19.0 compiler. Its eight dependency reports cover Boolean-word Hamming additivity, zero-distance equality, the equivalence with pairwise distinctness and consecutive-only adjacency, the exact product-pair criterion, the distance cases, and interval/relation substitution soundness. The relation interface retains an explicit premise covering every original indexed pair, including pairs assigned to the same variable. No additional assumption about slice isometries is used.

The module does not certify the concrete bitset tables, interval generation, translation/first-edge normalization, exhaustive search trees, or the concrete excluded-isometry witnesses. Those links are written and natively evaluated here; their Lean assembly is pending. The general criterion must not be described as a Lean certificate for the 70 exclusions.

The earlier round205 records remain immutable: 254 explicit finite slice models have complete Lean assignment coverage, but their geometric-domain, table and global-leaf connections remain separate unresolved obligations. The new model directly uses all coordinate words, which may simplify a future geometric connection. No such simplification has yet been completed in Lean.

## Frontier and next step

The two-coordinate component-switch symmetry acts on whole embeddings. The new census shows that even arbitrary four-coordinate history changes preserve this particular parent's cube class. It is therefore insufficient to search for a more elaborate four-coordinate symmetry of this saved path.

The next constructive step is the 55 unresolved five-coordinate models. The normalization still leaves permutations of the other four free coordinates. Quotienting this residual group could remove up to 24 equivalent labelled assignments; an exact representative rule and complete branch coverage are required before using it for exclusions. This is a proposed improvement, not a measured speedup. If it also yields exhaustion, the next alternatives are six free coordinates, a different parent, or changed length/order. A new five-coordinate witness would supply a different Q8 parent for subsequent Q9 joining; it would not itself improve the 191-edge Q9 construction.

For proof completion, record finite search trees for the 70 exhausted models and connect them to the checked whole-path criterion, normalization and explicit global-isometry witnesses. Neither task has been started as another round. The user requested a pause after round206.

The numerical Q9 frontier is unchanged: 191 is supported by a checked construction; the archived contributor upper-bound argument of 235 still awaits its full independent rebuild, and the retained 233/234 comparisons remain conditional. The prediction 196 is unresolved.

The contributor branch was refreshed to `1768329528c0b9e18017c692b09e15a3bdd42fc9`. Its latest total is 3,118 of 3,127 modules at 08:56 UTC on 14 November 2026. A 09:40 update reports another remote memory failure and a scheduled retry, without a new completion count. This is contributor-reported progress; no merge or independent rebuild was performed.
