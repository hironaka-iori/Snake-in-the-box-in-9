# Extension of three-coordinate histories

This is a written proof review. No computation or compiler was run. The extension theorem is valid. Its application to the saved path inherits the verification status and orientation convention of the all-partition rigidity result.

## Partial extension in the three-dimensional cube

Let $S\subseteq Q_3$, and let $f:S\to Q_3$ be injective, preserve parity, and preserve adjacency and nonadjacency of every selected pair. Then $f$ extends to a parity-preserving cube isometry of $Q_3$.

For a block word $u$, define its even antipodal representative by

$$
c(u)=
\begin{cases}
u,&\text{if }u\text{ is even},\\
u\oplus111,&\text{if }u\text{ is odd}.
\end{cases}
$$

The four even words label the four antipodal pairs. Distinct words of the same parity have different labels. For words of opposite parity, equal labels mean distance three, while different labels mean distance one.

The proposed assignment $c(u)\mapsto c(f(u))$ is well-defined. If two distinct selected words have the same label, they are opposite-parity antipodes. Their images remain opposite in parity and nonadjacent, so they remain antipodes and have the same label.

This label assignment is injective. For two words with different labels and equal parity, their images have equal parity and are distinct by injectivity, hence have different labels. For opposite parities, different source labels mean adjacency, so their images are adjacent and also have different labels. It therefore extends to a permutation of all four labels.

Every permutation of these four labels is realized by a parity-preserving cube isometry. Indeed, the maps

$$
u\longmapsto\pi(u)\oplus b,
\qquad \pi\in S_3,\quad b\text{ even},
$$

form a group of order $6\cdot4=24$. Its action on the four even words is faithful: an element fixing all even words fixes zero, so $b=0$; fixing all three weight-two words then forces $\pi$ to fix each coordinate. Thus its image in the permutation group of the four labels has order $24$ and is the whole group.

Choose an isometry realizing the extended label permutation. It sends each selected word to $f(u)$ because a label together with parity uniquely specifies a word. This proves the extension theorem, including empty and singleton selected sets.

## Application to ordered cube paths

Let $P=((z_i,u_i))_{i=0}^{m}$ and $Q=((z_i,v_i))_{i=0}^{m}$ be nonempty ordered induced paths, with three block coordinates and identical indexed base words. Both full-vertex parities change at every step, so their parity difference is constant. Since the base words agree, their block-parity difference is the same constant. Apply one fixed global block-bit flip to the target if that difference is odd.

In each base slice, the resulting selected correspondence is injective and parity-preserving. It preserves adjacency and nonadjacency because both full paths are induced with the same indexing; within a slice, full adjacency is precisely block adjacency. The extension theorem therefore supplies a cube isometry for each occupied slice. Empty slices may use the identity. Undoing the normalization composes each slice isometry with the same block-bit flip, which is still a cube isometry.

Consequently every target obtained by changing only three indexed coordinate histories belongs to the arbitrary-slice-isometry family. The same implication holds for fewer than three changed histories by enlarging the chosen block to three coordinates.

If all-partition rigidity holds for the saved $98$-edge $Q_8$ path, every such target belongs to the cube-isometry class guaranteed by that rigidity statement. A target in a genuinely different class must therefore change at least four coordinate histories, at the same length and with the fixed index matching.

### Orientation and verification qualifications

The native canonicalization minimizes over path reversal. Its recorded conclusion identifies paths up to a global cube isometry **and possible reversal of the ordered list**. Therefore the preceding four-history consequence inherits that equivalence relation. It does not establish that every target has a global isometry sending each source index to the same target index. A claim about direction-preserving ordered cube-isometry classes requires forward leaf witnesses or a separate argument removing reversal.

The extension theorem above is a written proof. The application to the saved path uses the native all-partition conclusion unless and until its domain completeness, compatibility interpretation, finite coverage, and leaf witnesses are all connected to checked Lean theorems. This review does not upgrade that native conclusion to a kernel-checked result.

## Sharpness of the local extension statement

In $Q_4$, the selected correspondence

$$
0000\longmapsto0000,\qquad0011\longmapsto1111
$$

is injective and parity-preserving. The two source vertices and the two target vertices are nonadjacent, so all selected-pair adjacency and nonadjacency relations agree. Their distances are respectively two and four. No cube isometry can extend the correspondence, because cube isometries preserve Hamming distance.

Thus the partial extension theorem fails for arbitrary selected subsets of a four-coordinate block. This example is local: it does not construct two whole induced paths with matching base histories, nor show that changing four histories escapes the saved path's cube-isometry class. It identifies the first block dimension where the general extension argument ceases to apply.
