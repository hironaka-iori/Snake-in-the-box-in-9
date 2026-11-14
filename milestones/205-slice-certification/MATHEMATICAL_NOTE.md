# Two-coordinate history classification and finite slice certificates

## Result and scope

This round gives an exact classification of whole ordered snakes whose coordinates may change in only two fixed positions. It also prepares a proof-assistant certificate for the finite slice models of the saved 98-edge Q8 parent. These are separate results. No longer Q9 snake, new unconditional numerical bound, or proof that 196 is optimal is obtained.

The classification below has a complete written proof and independent proof review. Its parity and diagonal-extension lemmas are checked in Lean. The complete geometric theorem and counting argument are not yet assembled in Lean. The source-specific active graphs now have accepted Lean spanning-tree certificates; earlier unchunked attempts exceeded the existing memory limit. Lean accepts complete coverage for 254 of the 254 explicit finite models, using 625 of the 625 planned data, elimination and cover modules. This statement concerns assignments to the literal domains and compatibility tables.

## Exact whole-path classification

Let P=((z_i,u_i)) for i=0,...,m be a nonempty ordered induced path in a cube. The two selected coordinates form u_i in Q2; z_i records every other coordinate. We classify all ordered induced paths Q=((z_i,v_i)) with exactly the same base word at each corresponding index. Length and index order are fixed. The initial block word and endpoints are unrestricted.

For each parity epsilon, take the set B_epsilon of base words z_i for which u_i has parity epsilon, with adjacency inherited from the base cube. Let c_epsilon count its connected components, with zero for an empty graph.

**Theorem.** All such Q are parametrized uniquely by one common parity offset and one binary switch for each component of B_0 and B_1. Consequently their number is

\[
2^{1+c_0+c_1}.
\]

Let r be the number of nonempty parity graphs. The number of classes under global isometries acting only on the two selected coordinates is

\[
2^{c_0+c_1-r}.
\]

This last formula does not count classes under arbitrary isometries of the full cube or reversal. Those operations can identify further paths.

**Proof.** Both full-vertex parities change at each path step. Their difference is therefore constant. The indexed base words agree, so the two block parities also differ by one constant delta. Fix a flip X of the first block coordinate and replace Q by X^delta Q. The resulting correspondence preserves block parity.

At a fixed base word and fixed parity, the selected correspondence is injective. A source vertex cannot occur at two indices, and the target also has distinct vertices. A nonempty subset of a two-element parity diagonal therefore has a unique extension to either the identity or its transposition. Write tau_0 for the map exchanging 00 and 11 and fixing 01 and 10; write tau_1 for the map exchanging 01 and 10 and fixing 00 and 11. Both are square isometries, and they commute. The first is coordinate swap followed by flipping both bits; the second is coordinate swap. Thus the normalized target is obtained by choosing a binary switch at every occupied base word of each parity.

These switches must agree on adjacent active base words. Choose a selected block word of the given parity in each of two neighbouring base slices. In a two-element diagonal, switching just one word toggles whether the two words are equal. Full adjacency between these slices is exactly equality of the block words. Since P and Q are induced paths in the same index order, every selected pair has the same adjacency status in each. Unequal switches would contradict this fact. A switch is consequently constant on each active component.

Conversely, independently choose a switch on each component. In one slice, the two diagonal actions combine into a square isometry and preserve distinctness and adjacency. Between slices at base distance at least two there is no possible edge. Between neighbouring slices, opposite block parities remain unequal, while same-parity words receive the same switch because their base words lie in one active component. Their equality is preserved. Every selected edge and nonedge is therefore preserved. Applying X^delta afterwards is a global cube isometry, so every parameter choice gives an induced path.

Different offsets give different block parities at every index. For a fixed offset, different component choices change a word in an occupied component. Hence the parameters are bijective, proving the first count.

The eight square isometries act on this family. A parity-changing isometry fixes no selected block word. Among the four parity-preserving maps, only switches on unoccupied diagonals fix the entire ordered target. The stabilizer has size 2^(2-r), so every orbit has size 2^(r+1). Dividing the first count by this orbit size proves the second formula.

**Rigidity consequence.** If each nonempty active graph is connected, all these targets are images of P under a single global square isometry. The conclusion covers arbitrary changes to the two coordinate histories; local isometry extensions are deduced in the proof. It applies to the entire ordered snake.

**Symmetry of whole embeddings.** For each active component, interchange the two words of its parity diagonal in every base slice of that component, simultaneously along the entire snake. Each such transformation is an involution. Switches on different components commute: they have disjoint supports within one parity, and the two diagonal actions commute across parities. Their independent products form a group isomorphic to (Z/2Z)^(c0+c1), acting freely and transitively on the targets with the original block parity at each index. Thus the symmetry acts on whole ordered embeddings. A switch need not fix the source vertex set or preserve adjacency outside the selected paths. The common parity offset supplies the other half of the targets; no assertion is made that all allowed ambient maps including that offset form one group for a fixed source.

**Boundary cases.** A one-vertex path has four possible block words and one class. If only one block parity occurs along any connected path, no step changes a block coordinate, so that word is constant; its active base graph is connected and the same counts apply. If both parities occur and both active graphs are connected, there are eight ordered targets, all in one class under the block isometries.

## One-coordinate version

If only one coordinate may change and every other indexed coordinate is fixed, the difference of the two full-vertex parities is exactly the xor difference of that coordinate. It is constant along the path. Thus there are exactly two coordinate histories, related by a global bit flip. Consecutive cube adjacency suffices; inducedness is unnecessary for this assertion. HistoryParity205 checks this constant-offset argument.

## Application to the saved Q8 parent

The same 99-vertex input used in rounds 188, 203 and 204 is pinned in data/lower-dimensional-input.json. For all 28 coordinate pairs, both active graphs are connected in the native calculation. The 56 explicit spanning trees, source-position witnesses, and complete coverage indices are in data/active-trees.json. Under the written theorem this leaves only the eight global block-isometric ordered targets for each coordinate pair.

This excludes a new cube class from changing only one or two coordinate histories of this particular parent. The three-coordinate case is treated next. Changing length, changing index order, or starting from a different parent remains unrestricted by this result. In blocks of at least four coordinates, selected-slice correspondences need not extend to cube isometries; such correspondences are outside the exhausted round204 family.

The general spanning-tree constancy theorem and all 56 source-specific graph certificates pass Lean. The initial quantified and Boolean-list versions were stopped by the 256 MiB guard. Splitting the finite assertions into eight-position lemmas resolved that failure. The complete geometric theorem and counting assembly remain pending.

## Three-coordinate extension and the four-coordinate boundary

**Theorem.** An injective, parity-preserving map from any selected subset of Q3 into Q3 that preserves adjacency and nonadjacency of all selected pairs extends to a parity-preserving cube isometry.

**Proof.** Label each antipodal pair by its even word: c(u)=u for even u and c(u)=u xor 111 for odd u. There are four labels. Among equal-parity words, equality of labels is exactly equality of words. Among opposite-parity words, equal labels mean distance three and different labels mean adjacency.

The selected map induces a well-defined injective map on its represented labels. Selected antipodes stay opposite in parity and nonadjacent, hence antipodal, so one source label cannot split. Different labels stay different: use injectivity for equal parity and preserved adjacency for opposite parity. Extend this partial injection to a permutation of the four labels.

Every such permutation is realized by a parity-preserving cube isometry. There are 24 maps u -> pi(u) xor b, with six coordinate permutations pi and four even translations b. Their action on the four even words is faithful: fixing zero forces b=0, and fixing each weight-two word fixes its missing coordinate and thus forces pi to be identity. These 24 actions are therefore all permutations of the four labels. Choose the action extending the selected label map. Label and parity uniquely determine a word, so it agrees with the selected correspondence everywhere. Empty selected subsets cause no exception.

For two ordered induced paths with the same indexed base words outside three coordinates, the common parity-offset argument normalizes the target parity. Each selected-slice correspondence then meets the theorem's hypotheses and extends to a cube isometry. Undoing the global normalization still gives one cube isometry per slice. Thus **arbitrary changes to three coordinate histories already belong to the slice-isometry family**, without assuming these extensions in advance.

Combining this theorem with round204's native all-partition rigidity shows that changing at most three histories cannot produce a new class of the saved 98-edge Q8 parent, where equivalence allows a global cube isometry and possible path reversal. A different class at the same length and fixed index comparison therefore requires at least four changed coordinate histories. This consequence inherits the native census's evidence level and its reversal convention. It does not assert a forward global isometry at every corresponding index.

The extension theorem fails in Q4 even for whole induced paths. Take P=(0,1,3,7,6) and Q=(0,1,3,7,15), with integers interpreted as four-bit words. Both have four edges, and corresponding vertices have equal parity. The indexed correspondence preserves every selected edge and nonedge. Their endpoint distances are two and four, so no cube isometry can carry one path to the other, even allowing reversal. Lean checks both entire paths, distinctness, parity alignment and endpoint distances. This supplies a small sharpness example for the extension theorem; it constructs no new Q8 parent or Q9 record.

The written proof and its orientation qualification are independently reviewed in logs/three-coordinate-extension-review.md. Lean checks the three-coordinate parity/antipodal identities, the induced injective correspondence of selected labels, and two complete four-dimensional paths with different endpoint distances. The full extension theorem and the geometry-to-census consequence still await assembled Lean proofs.

The same native calculation on the saved 26-edge Q6 and 50-edge Q7 inputs also finds one restricted block-isometry class for every coordinate pair: 15 of 15 and 21 of 21, respectively. The Q8 result is 28 of 28. These are comparisons of one saved parent in each dimension, with fixed length and indexed base words; they do not establish a universal dimensional recurrence. See data/dimension-history-counts.json.

## Finite slice-model coverage

For each of the 254 nontrivial coordinate partitions, root normalization fixes one occupied slice map to identity. A fixed tree of actual snake crossings then builds absolute candidate domains from complete relative-map lists. Maps are identified only when they agree pointwise on the selected words of that slice. The prepared model has 5,821 variables and 23,892 initial candidate values in total. Its tables have 460,858 Boolean entries. Initial arc propagation removes 16,166 values, leaving 7,726; residual branching yields 321 complete assignments across the 254 models.

A value can be removed only after every value in the entire current neighbouring domain has been checked incompatible. The Lean elimination theorem preserves every complete compatible assignment under this removal. Each remaining branch enumerates every value in its current domain. An empty domain excludes that branch; a complete assignment is an explicit leaf. The generated coverage theorem therefore concerns all assignments satisfying the stated literal finite domains and compatibility tables.

The files are split to stay within the resource budget. This is a certificate of finite-model coverage. Three geometric obligations remain separate:

1. Every admissible geometric slice assignment reaches the finite candidate domains, including the classification and completeness of relative cube-isometry lists.
2. Each literal table entry expresses exactly the selected-word compatibility condition, with correct indices and orientation.
3. Each surviving leaf is the image of the source under an explicit global cube isometry, possibly after reversal.

The fixed-tree domain-completeness argument has a written proof and independent source review. In the induction, replacing a parent map by one agreeing on its selected words preserves the required relative-map conditions for the desired child map. The selected-image representative can therefore be chosen at every child. This justifies pointwise deduplication mathematically; its full finite data bridge remains to be checked in Lean.

For all 321 leaves, data/leaf-witnesses.json now supplies a concrete coordinate permutation, translation, orientation and image list. The native script compares all 99 indexed vertices with that explicit isometry. These witnesses remove dependence on a canonicalization routine from the future leaf-certificate design; their Lean replay is still pending.

All 321 witnesses use forward index order; none needs reversal. They provide explicit candidate certificates for the stronger ordered conclusion. The four-history consequence above is stated with the retained comparison's reversal convention, and no ordered Lean conclusion is claimed before the geometric connections and witness replay are complete.

## Evidence and continuation

The independent reports are logs/history-rigidity-review.md, logs/history-count-review.md and logs/certificate-design-review.md. They are written reviews, not compiler receipts. Accepted Lean receipts and exact source, object and log hashes are collected in data/completion.json. Failed attempts retain their source and compiler output under logs.

The next useful proof work is to assemble the coordinate-history theorems from the accepted lemmas, then connect the finite slice coverage to its geometric domains and explicit leaf witnesses. A construction search on this parent should permit at least four changed coordinate histories and selected-slice correspondences beyond full slice isometries. No claim is made that this wider search will produce a longer snake.

The user requested a pause after this round. Save and publish the checkpoint, pause the goal, and resume only upon a subsequent user instruction.
