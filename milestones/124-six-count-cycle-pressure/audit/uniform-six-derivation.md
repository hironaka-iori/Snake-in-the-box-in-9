# Conditional bounds from a universal six-count floor

Status: complete Lean proof source prepared in `lean/UniformSixBound124.lean`; no compiler has been run for this task. The source imports `ReferenceInterface`, introduces no definitions or additional axioms, and requests four axiom reports. Compilation and its resulting evidence remain the parent's responsibility.

Let $\alpha_0,\ldots,\alpha_m$ be natural-number counts, with endpoints at least 4 and every internal count at least 1. Assume explicitly that every six consecutive internal positions satisfy

$$
L\le\sum_{j=0}^{5}\alpha_{r+j}
\qquad (1\le r,\ r+5<m).
$$

The source's `disjoint_six_blocks` theorem proves by induction that the first $6B$ internal positions have total at least $BL$, provided the $B$ blocks beginning at $6b+1$ each satisfy that floor. It uses the standard finite-sum concatenation identity; no overlapping contributions are counted twice.

`total_lower_of_six_floor` applies this to any $6B+1\le m$. The remaining internal indices are $6B+1,\ldots,m-1$, exactly $m-(6B+1)$ positions. Their count lower bound 1, together with the two endpoint lower bounds, yields

$$
\sum_{i=0}^{m}\alpha_i
\ge BL+\bigl(m-(6B+1)\bigr)+8.
$$

The general theorem requires $m\ge1$, through $6B+1\le m$, so its two endpoints are distinct indices. It includes $B=0$. Both numerical theorems handle small $m$ through a proof by contradiction: the decomposition is used only after assuming that $m$ exceeds the proposed bound. No special interpretation of coincident endpoints at $m=0$ enters the argument.

For the first numerical consequence, suppose $m\ge234$ and set $B=38$. The 38 disjoint blocks cover internal positions 1 through 228. If the universal floor is 26, then

$$
T:=\sum_{i=0}^{m}\alpha_i
\ge38\cdot26+(m-229)+8=m+767.
$$

Combining this with the explicit square inequality $T+35(m+1)\le9214$ gives

$$
36m+802\le9214.
$$

At $m=234$ the left side is 9226, exceeding 9214 by 12. Therefore `bound233_of_floor26` concludes $m\le233$.

For the second consequence, assume $m\ge235$ and retain the same 38 blocks. Universal floor 25 instead gives $T\ge m+729$, hence

$$
36m+764\le9214.
$$

At $m=235$ the left side is 9224, exceeding 9214 by 10. Therefore `bound234_of_floor25` concludes $m\le234$.

The exact source interface is in namespace `Snake9.UniformSix124`:

- `disjoint_six_blocks`: finite-sum lower bound from the individual disjoint-block inequalities.
- `total_lower_of_six_floor`: total-count lower bound, retaining the universal local floor, internal positivity, endpoint bounds, and block-fit condition.
- `bound233_of_floor26`: endpoint and internal bounds, the universal floor26 hypothesis, and the square inequality imply $m\le233$.
- `bound234_of_floor25`: the corresponding floor25 hypotheses imply $m\le234$.

These are conditional arithmetic consequences. The pattern-specific native probes in milestone123 concern the direction word $0123042$ and do not supply either universal hypothesis. This source provides no new local refutation, actual-snake universal count theorem, or unconditional improvement to the snake-length bound. The finite-sum proof uses ordinary induction and arithmetic tactics; no finite enumeration, solver, `native_decide`, or placeholder proof is present.
