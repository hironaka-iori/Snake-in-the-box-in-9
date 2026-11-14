# Residual coordinate symmetry and domain pruning

This is a written mathematical review. No search or compiler was run. The proposed pruning rule is sound, subject to the group-invariance and integration obligations below.

## Orbit coverage

After normalizing the first block word to zero and the first block transition to the first unit word, the coordinate permutations fixing that direction form the residual group. For five block coordinates this group is $S_4$, with 24 elements. Each element acts componentwise on the chronological tuple of interval words.

Every such permutation preserves Hamming distance, word parity, zero, and the first unit word. It therefore preserves all geometric constraints of the exact fixed-base-history model and both normalizations. The fixed base coordinates and the index-to-interval map are unchanged.

Each orbit is finite and consequently has a lexicographically least tuple. If $x$ is such a tuple, then

$$
x\le_{\mathrm{lex}}\pi(x)
\qquad\text{for every residual permutation }\pi.
$$

Conversely, imposing all these inequalities chooses the least tuple of each orbit. Different permutations may give the same tuple; no freeness assumption or division by the group order is needed. Using only some of the inequalities remains safe for orbit coverage, although it need not select a unique representative.

The chronological interval tuple is an appropriate representation. Expanding each interval value into its consecutive source positions preserves the first index of disagreement between two interval assignments. Thus lexicographic comparison of interval words agrees with comparison of their expanded block-word sequences. More fundamentally, any fixed total ordering of the finite interval assignments would suffice for orbit coverage. No claim that these are all ambient cube-isometry representatives is required.

## Pruning at a domain with a fixed prefix

Fix a permutation $\pi$, domains $D_0,\ldots,D_{n-1}$, and an index $j$. Suppose

$$
\pi(u)=u\qquad\text{for every }i<j\text{ and every }u\in D_i.
$$

Every assignment drawn from the domains then agrees with its image under $\pi$ before position $j$. If its value at $j$ satisfies $u>\pi(u)$, position $j$ is the first difference and the assignment violates the required lexicographic inequality. Removing every such value is therefore sound.

After this deletion, scanning may continue only if every remaining value at position $j$ is fixed by $\pi$. If any value satisfies $u<\pi(u)$, choosing that value makes the lexicographic inequality strict already at $j$; later values can have either comparison sign. For example, an earlier value $u$ with $u<\pi(u)$ permits a later value $v$ with $v>\pi(v)$. Pruning the later value solely from this permutation would be unsound. A mixture of fixed and strictly smaller values also requires stopping, because the scan must preserve assignments choosing either type.

If deletion empties a domain, the branch has no lex-admissible completion. The empty domain must be treated as failure, rather than using vacuous fixedness to assert successful propagation. If every remaining value is fixed, the enlarged prefix satisfies the same hypothesis and the argument repeats.

The rule applies to permutations of any order; it does not assume an involution. Repeating it for different permutations, or after other sound domain reductions, remains sound. The invariant is that every lex-admissible complete assignment previously represented by the domains remains represented after each deletion.

An equivalent implementation can continue past earlier singleton domains when their sole value is fixed. It cannot continue merely because the earlier domains are singletons: an earlier singleton with value strictly smaller than its image already satisfies the lexicographic condition and requires stopping.

## Branching and excluded assignments

The lex inequalities are global root constraints. They can be propagated inside arbitrary search branches without requiring each branch to be group-invariant: complete root branching still visits the retained representative's branch. Independently launching a restricted subproblem and imposing the full group's inequalities requires a separate coverage argument if that subproblem is not invariant.

The exclusion list deserves particular care. For an exact claim that the residual search preserves every orbit of the model *after* forbidden assignments are removed, the forbidden set must be invariant under the residual group. Otherwise the orbit minimum might be forbidden while another member remains allowed. Removing that other member by lex pruning would no longer preserve a solution of the model with those exclusions. Explicit witnesses that excluded tuples are isometric do not alone prove this closure. Generating the full residual orbit of each excluded tuple is sufficient.

For the narrower goal of ruling out a new ambient cube class, a weaker argument is enough: every forbidden tuple is in the original cube class, so the entire orbit of a genuinely new-class solution avoids all forbidden tuples. That orbit still contains an allowed lex minimum. This proves coverage for the new-class question even if the excluded list is not invariant. It should not be described as unrestricted solution coverage of the excluded finite model.

Any further endpoint restriction, omission limit, or source-dependent auxiliary constraint must likewise be checked for invariance, or its permitted subgroup reduced. The exact base-history relations themselves have the required invariance.

## Lean draft and remaining obligations

The accompanying `lean/LexDomain207.lean` is an uncompiled `Std`-only draft. It defines ordinary lexicographic order on lists of natural numbers; proves reflexivity, totality, and transitivity; constructs a minimum of a finite nonempty list; derives a leader for a finite family closed under listed actions; and proves that deleting values greater than their permutation image preserves a lex-admissible assignment when its preceding values are fixed.

The core pruning theorem does not require that its map be a permutation. Group structure is needed for the geometric orbit-coverage application, not for this local implication. The finite-family theorem applies to each orbit once its finite enumeration, nonemptiness, and closure have been supplied.

This draft does not establish that the concrete word maps are the intended coordinate permutations, that all earlier domain values are actually fixed, that the candidate tuple satisfies every needed lex inequality, or that the native scan implements the proved deletion. It also does not prove compatibility-table invariance, excluded-set closure, complete branching, or a concrete exhaustion result. These are explicit model-integration obligations.
