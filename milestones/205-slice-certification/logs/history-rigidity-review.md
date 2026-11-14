# Two-coordinate history rigidity

This is a written proof. No computation or compiler was run.

## Statement

Let $P=(p_0,\ldots,p_m)$ and $Q=(q_0,\ldots,q_m)$ be ordered induced paths in the same cube. Choose two coordinates as the block and write

$$
p_i=(z_i,u_i),\qquad q_i=(z_i,v_i),\qquad u_i,v_i\in Q_2.
$$

Thus the two paths have identical base coordinates at every corresponding index. For each parity $\varepsilon$, let $B_\varepsilon$ be the set of base words $z_i$ for which $u_i$ has parity $\varepsilon$, with adjacency inherited from the base cube.

If each nonempty $B_\varepsilon$ is connected, there is one cube isometry acting only on the two block coordinates that sends $p_i$ to $q_i$ for every $i$. No initial assumption that the slice correspondences extend to cube isometries is required.

## Proof

Both full-vertex parities change at every path step. Their difference is therefore constant along the ordered paths. Since their base words agree, the parity difference between $u_i$ and $v_i$ is the same constant. If necessary, apply one global block-bit flip to $Q$. It suffices to prove the assertion after this normalization, when $u_i$ and $v_i$ have the same block parity for every $i$.

Fix a base word $z$ and parity $\varepsilon$. The selected correspondence $u_i\mapsto v_i$ at this base is an injection: each path has distinct vertices, and the base words agree. It maps a subset of a two-element parity diagonal into that same diagonal. If the subset is nonempty, this injection extends uniquely to either the identity or the transposition of the diagonal. If the subset is empty, choose the identity.

Let $\tau_0$ exchange $00$ with $11$ and fix the odd diagonal, and let $\tau_1$ exchange $01$ with $10$ and fix the even diagonal. There are consequently binary selectors $f_0(z),f_1(z)$ such that the normalized image of every selected word is

$$
v_i=\tau_0^{f_0(z_i)}\tau_1^{f_1(z_i)}(u_i).
$$

The two maps commute. Each is a $Q_2$ cube isometry: $\tau_1$ swaps the coordinates, while $\tau_0$ swaps them and flips both. In particular, the pointwise correspondence has now been shown to admit a slice-isometry extension.

The effects of the two selectors on selected-pair adjacency are independent. Opposite-parity block words always have block distance one, whatever the selectors; their full vertices are adjacent exactly when their base words coincide. Same-parity block words have distance zero or two. Distinct such vertices in the same slice remain distinct and nonadjacent. For neighbouring base words, full adjacency is exactly equality of the block words. For base distance at least two, full adjacency is impossible.

Because both ordered paths are induced, the combined map preserves adjacency and nonadjacency of every selected pair: in each path two different selected vertices are adjacent exactly when their indices differ by one. For same-parity pairs, only the corresponding selector can affect this relation. Therefore each controlled diagonal switch separately preserves every selected-pair relation on the original path.

If $z$ and $w$ are adjacent vertices of $B_\varepsilon$, select one block word of parity $\varepsilon$ in each slice. Unequal selector values $f_\varepsilon(z)$ and $f_\varepsilon(w)$ toggle equality of these words, since that diagonal has only two elements. This would toggle full adjacency, contrary to the preceding paragraph. Hence $f_\varepsilon$ is constant on every component of $B_\varepsilon$.

Connectedness gives a single value $\alpha_\varepsilon$ on every nonempty $B_\varepsilon$; choose an arbitrary value when it is empty. The normalized image of all selected vertices is thus given by the one global block isometry $\tau_0^{\alpha_0}\tau_1^{\alpha_1}$. Undoing the initial block-bit flip proves the claim, with the original index order preserved.

## One-coordinate version

If $P$ and $Q$ have identical coordinates at every index except for one chosen coordinate, the same total-parity argument shows that their differing bits have one constant xor value. A single global flip, or the identity, sends every $p_i$ to $q_i$. Inducedness is unnecessary for this one-coordinate assertion; consecutive cube adjacency already supplies the parity argument.

## Scope and consequence

For two coordinates, active-graph connectedness is a sufficient condition. It is not claimed necessary. The proof uses the complete ordered base-word sequence, including repetitions, and both paths' inducedness. Merely preserving the set of occupied base words is insufficient for this argument. For noninduced paths, added chords need not contradict the path hypothesis, so the component-constancy deduction would require a separate pair-preservation assumption.

Applied to the saved $Q_8$ path, kernel certificates that both active graphs are connected for every coordinate pair would exclude any nonisometric ordered induced embedding obtained by changing only those two coordinate histories. This is stronger in its initial hypotheses than an arbitrary-slice-isometry statement: the required local extensions are derived. It does not address changing three or more coordinate histories, inserting or deleting vertices, or a different source path. This report does not itself certify the saved path's finite connectedness data.
