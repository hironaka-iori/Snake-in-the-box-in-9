# A weight invariant of the hypercube odd-neighbour map

Let D(S) consist of the vertices of a d-dimensional cube with an odd number of neighbours in the finite set S. For every d and every S,

**|D(S)| ≡ d |S| (mod 4).**

For any fixed vertex x the number of neighbours of x lying in D(S) is congruent modulo two to d times the indicator of x in S. To see this, count length-two walks from x into S. There are d return walks. Each vertex at distance two is reached in exactly two ways, and every other vertex distinct from x contributes zero. Now toggle a new x into S. The set D(S) changes by symmetric difference with all d neighbours of x, so its weight changes by d minus twice the number of those neighbours already in D(S). Since x was absent, that number is even. The change is d modulo four. Starting with the empty set and introducing each vertex once proves the assertion.

In Q9 the map therefore preserves Hamming weight modulo four. Together with its linearity this gives **|D(S) △ D(T)| ≡ |S △ T| (mod 4)** for every pair of sets. It applies separately on either bipartition class. In particular a 192-edge snake with 97 vertices on one parity and 96 on the other must have odd-neighbour signatures on the opposite parities of sizes **1 and 0 modulo four**, respectively. It also gives **|S △ D(S)| ≡ 2|S| (mod 4)** in Q9: |S ∩ D(S)| counts the odd-degree vertices of the graph induced by S and is even. This last statement applies to arbitrary vertex sets, including those whose induced graph has many components.

For a finer invariant let N₂(S) be the number of unordered pairs of its vertices at cube distance two. Let N₃(S) count, for every cube vertex v, the unordered triples of distinct members of S adjacent to v, summed over all v. Then in every dimension

**|D(S)| ≡ d|S| − 4N₂(S) + 4N₃(S) (mod 8).**

Indeed, for any integer c≥0 its oddness indicator equals c − 2 binom(c,2) + 4 binom(c,3) modulo eight, by expanding (1−(1−2)ᶜ)/2. Sum this formula for the number of selected neighbours at every vertex. The linear term sums to d|S|. Each pair at distance two is counted twice in the binomial second moment, once at each common neighbour. The cubic term is N₃(S) by definition.

The computation checks the general identities on all 65,536 subsets of Q4, then on the full set and the two parity classes of each of the 131 Q9 bank snakes. The arguments above do not depend on this finite computation. [Checks](syndrome_mod_four.py), [Q9 incidence counts](syndrome-mod-four.json), [odd-neighbour inversion](SYNDROME.md).

The modulo-four result has a separate formal proof in Lean 4.19 for all finite cube dimensions. It proves that the parity of the intersection of D(A) with B equals that of D(B) with A, then uses the two slices of the next higher cube to prove the weight identity by induction. The Lean axiom audit reports `propext` and `Quot.sound` for both the adjointness and weight theorems. The modulo-eight refinement above has the counting proof and finite checks. [Lean source](SyndromeWeight.lean).

There is a small search consequence for a hypothetical 192-edge snake. Translate so its 97-vertex side is even. Write e and o for the even and odd sizes of D(S), respectively. Since e≡0 and o≡1 modulo four, and since applying D twice restores S, we have 9e≥96 and 9o≥97. Thus e≥12, o≥13. Moreover S∩D(S) consists precisely of its two even endpoints, so e≤256−97+2 and o≤256−96. Rounding these bounds to their residue classes gives e≤160 and o≤157. In particular **25≤|D(S)|≤317 and |D(S)|≡1 (mod 4)**. For two possible signatures of the same 97-member parity set size, a symmetric difference of exactly six sites requires one, three or five of the switched sites to have belonged to the old signature: six minus twice that number must be divisible by four.
