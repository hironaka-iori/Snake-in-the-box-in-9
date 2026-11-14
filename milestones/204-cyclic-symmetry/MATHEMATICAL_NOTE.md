# Whole-snake gluing of coordinate-slice isometries

Round 204 began with the hypothesis that a controlled order-three rotation could change the saved 98-edge Q8 parent's cube-isometry class. The finite investigation refutes that hypothesis for this parent and gives a broader restriction: independently choosing an arbitrary cube isometry in every slice of any coordinate partition still produces only its original cube class, whenever every snake pair relation is preserved. General criteria and concrete obstructions pass Lean; the complete 254-partition enumeration remains native. No longer Q9 snake or improved global bound is established.

The user requested a pause after this round. Publication and compilation precede the goal pause. Resume only on a new user request.

## Exact whole-snake criterion

Partition the coordinates, write vertices as $(z,u)$, and assign a block cube isometry $g_z$ independently to each base word. Define

$$F(z,u)=(z,g_z(u)).$$

For neighbouring base words $z,w$, put $A=S_z$, $B=S_w$ and $r=g_z^{-1}g_w$.

**Theorem.** Every adjacency and nonadjacency of the selected set is preserved exactly when, on every such pair,

$$r(c)=c\quad(c\in A\cap B),\qquad r(B\setminus A)\cap A=\varnothing.$$

**Proof.** In one slice both vertices undergo a common isometry. Slices at base distance at least two cannot supply an edge. Between neighbouring slices, image adjacency means $g_z(u)=g_w(v)$, equivalently $u=r(v)$. Requiring this exactly when $u=v$ fixes every common selected word and forbids any word of $B\setminus A$ from entering $A$. These conditions exhaust all pairs. The map is bijective, since each $g_z$ is, so distinct vertices stay distinct and the complete image is an induced snake.

The criterion protects actual crossings and separately prevents new crossings. It assumes neither a common generator nor a common isometry order. Common left multiplication of all $g_z$ is a global cube isometry; one occupied slice map may therefore be normalized to identity for classification up to cube isometry. If relative maps are assigned first, their products around closed base walks must be identity. The enumeration assigns actual maps and enforces that consistency directly.

## Crossing words restrict the relative maps

Suppose $C=A\cap B$ is nonempty and choose $c\in C$. Every cube isometry fixing $c$ has the form

$$r(x)=c\oplus\pi(x\oplus c),$$

where $\pi$ permutes the block coordinates. Form a matrix with rows $x\oplus c$ for $x\in C$. The permitted permutations are exactly those within classes of identical columns. Indeed, inspecting each coordinate of every fixed row proves necessity, and unchanged columns reconstruct all rows, proving sufficiency. Thus the pointwise stabilizer is the product of the symmetric groups on those column classes. The no-new-contact condition must still be imposed.

Distinct columns force the relative map to be identity. With $k$ block coordinates this sufficient condition requires at least $1+\lceil\log_2 k\rceil$ crossing words, because the anchor row is zero. Repeated columns can still yield rigidity through the no-new-contact condition. Lean checks the fixed-word/column equivalence and the distinct-column consequence. The standard representation of cube isometries by translation and coordinate permutation, and its enumeration interpretation, retain written-proof scope.

## Complete comparison on the saved Q8 parent

Every nonempty proper base-coordinate subset was examined:

| Base dimension | Block dimension | Partitions | Record |
|---|---|---|---|
| 1 | 7 | 8 | `data/face-isometries.json` |
| 2 | 6 | 28 | `data/slices-2.json` |
| 3 | 5 | 56 | `data/slice-images-3.json` |
| 4 | 4 | 70 | `data/slice-images-4.json` |
| 5 | 3 | 56 | `data/slice-images-5.json` |
| 6 | 2 | 28 | `data/slice-images-6.json` |
| 7 | 1 | 8 | `data/slice-images-7.json` |

All 254 partitions completed. Every image is in the original cube-isometry class. The two omitted trivial partitions give a global isometry or identity. For the eight single-coordinate cuts, crossing counts are $(14,21,5,13,26,4,7,8)$ and pointwise stabilizer sizes are $(2,1,4,2,1,4,2,1)$. Of these 17 relative candidates, only identity survives in each cut.

**Coverage argument.** Projecting the connected snake onto its base words gives a connected graph of occupied slices joined by actual crossings. Normalize one root map to identity. Choose an unassigned slice with an assigned crossing neighbour; enumerate all relative maps fixing the shared words using the anchor classification. Compose with the neighbour's map, then impose the exact matching criterion against every assigned adjacent slice, including slices with empty intersection. Every valid completion occurs in this recursion. Completed images are checked for all vertex pairs.

For base dimensions three through seven, maps equal on every selected word of a slice are identified. This preserves image completeness. If $g'_z$ replaces $g_z$ with the same selected images and a later desired map is $h$, then $(g'_z)^{-1}h$ still fixes every original common word and creates no extra contact. It belongs to the complete relative list and reconstructs $h$. Lean checks the selected-image transfer and reconstruction steps. The full recursion argument and source coverage have independent written review, without an independent census rerun.

Cube classes are compared by transition words with direction names normalized in order of first occurrence, taking the smaller forward/reversed word. This is complete: an isomorphism between the induced paths follows either their forward or reversed order, and matching normalized transition words give a coordinate permutation plus translation. Unused coordinates can be matched arbitrarily.

**Finite conclusion.** Every admissible map in this complete slice-isometry family takes the saved parent to a cube-isometric copy. Conjugating by a cube isometry transports the partition and local maps, so the family is equivariant. Induction extends the conclusion to arbitrary iterations with changing partitions.

This conclusion uses native enumeration and is not a complete Lean certificate. It concerns one saved 98-edge parent. It supersedes the suggestion that a different order of controlled block rotation might change this parent, since every such map is included. It does not cover arbitrary changes to the selected paths within slices, or transformations whose base coordinates depend on the block words.

## Order-three analysis and a concrete obstruction

For $h^3=\mathrm{id}$ and $f(z)\in\mathbb Z/3\mathbb Z$, set $g_z=h^{f(z)}$. For $d=f(z)-f(w)$, compatibility is

$$h^d(u)=v\quad\Longleftrightarrow\quad u=v\qquad(u\in S_z,v\in S_w).$$

A shared moved word forces $d=0$. Distinct selected words in one moved orbit forbid one nonzero residue. Combined restrictions can forbid both nonzero residues without any shared moved word. Each edge allows one of $\{0\}$, $\{0,1\}$, $\{0,2\}$ or $\{0,1,2\}$. The calculation contracts equality constraints and enumerates the remaining phases modulo a global rotation. If all selected block words are moved, actual path crossings force one phase throughout; this generic rigidity passes Lean. For composite orders, the appropriate hypothesis is trivial stabilizer, since moved words can have shorter orbits.

All 224 single-three-cycle choices and all 8960 two-three-cycle choices on the saved Q8 parent are rigid. These exhaust order-three coordinate-block isometries: there are at most two disjoint three-cycles; translations have even parity on each cycle; unchanged coordinates can be put in the base. There are four conjugating translation choices per cycle. Inverse generators give the same phase family and are identified.

The exceptional single-cycle choice rotates coordinates $(0,3,4)$ with zero conjugating translation. Its preliminary equality graph has two components, one the singleton base word 70. Rotating this fibre once changes endpoint 78 to 86, creating a chord to vertex 82 at index 73. Rotating it twice changes the endpoint to 71, creating a chord to vertex 7 at index 3. The native calculation preserves every consecutive edge in both cases. Lean checks the displayed nonconsecutive pairs and excludes both nonzero phases. The other 223 single-cycle cases and all two-cycle cases have connected equality graphs.

For the 131 saved Q9 snakes, all 44016 single-three-cycle choices and every compatible phase assignment were completed. The 194 nonzero assignments produce 34 existing bank classes and no new class. Exact totals appear in completion.json. Two-/three-cycle Q9 cases and arbitrary Q9 slice maps remain unexamined. Equivariance and one-step closure extend the saved-bank conclusion to mixed iterations with the earlier closed one-/two-pair families.

## Admissibility under repetition

Rotate block coordinates $0\to1\to2\to0$ only in the bit-3-one face of Q4. Then

$$
\begin{aligned}
S&=(5,1,0,8,10,11,15),\\
F(S)&=(5,1,0,8,12,14,15),\\
F^2(S)&=(5,1,0,8,9,13,15).
\end{aligned}
$$

The first two paths are induced; the third has a chord between positions 1 and 4 because vertices 1 and 9 are adjacent. Lean checks both complete valid paths, both image relations, the order-three identity on Q4, and the chord. Admissible assignments for one fixed snake therefore need not form a group under addition.

Any sequence admissible at each step with one fixed cyclic action nevertheless composes to a cumulative assignment admissible on the original snake. Enumeration of every original assignment covers such sequences. Changing blocks requires the separate cube-class closure argument. The independent review explains why a prescribed involutive factorization may fail while another succeeds; no general nonfactorization theorem is claimed.

## Verification and continuation

Five Lean modules pass with 28 dependency reports: general preservation and image path (5), cyclic identities and rigidity (8), the Q8 chord obstruction (3), relative matching/column/representative results (8), and the small repeated-rotation example (4). Failed elaboration attempts are preserved; accepted sources and objects are pinned. No accepted proof uses an unproved placeholder or native decision axiom.

The reviews assess written proofs and source coverage, without rerunning the finite censuses. The next certification step is to convert the complete 254-partition enumeration into a Lean-checkable completeness certificate. Both editor manuscripts are updated in place and mirrored; compilation and equality receipts are recorded in completion.json.

After a new user resume request, further construction work should change the selected paths within slices or use different Q8 parents. Repeating any controlled block rotation on this saved parent cannot escape the covered family. The earlier overlap-five/index3-or95 condition remains a necessary construction restriction, with existence unresolved. Archived upper bound 235 still awaits independent rebuild; 233/234 remain conditional. No optimality result for 191 or 196 follows.
