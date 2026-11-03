# Conditional bound with a total deficit allowance

Status: `lean/SixDeficit124.lean` is prepared and has not been compiled in this task. It imports the checked `UniformSixBound124` module and adds three theorems, with three requested axiom reports and no definitions. No solver, graph computation, or compiler was run.

For block sums $s_b=\sum_{j=0}^{5}\alpha_{6b+j+1}$, natural-number subtraction gives $L\le s_b+(L-s_b)$. Here $L-s_b$ is the nonnegative deficit, equal to $\max(0,L-s_b)$ when subtraction is interpreted over the integers. Induction over disjoint blocks, using the finite-sum concatenation identity, proves

$$
BL\le\sum_{i=1}^{6B}\alpha_i+
\sum_{b=0}^{B-1}(L-s_b).
$$

This is `blocks_with_deficits`. It holds for arbitrary natural-number counts, including $B=0$, without local lower-bound hypotheses.

To prove the conditional length bound, suppose $m\ge235$. Take $B=39$ and $L=25$. These blocks cover exactly the 234 internal positions 1 through 234. The remaining internal positions, 235 through $m-1$, number $m-235$. Let $D$ denote the sum of the 39 natural-number deficits. If each internal count is at least 1 and the two endpoint counts are at least 4, then

$$
T+D\ge975+(m-235)+8=m+748.
$$

The explicit hypothesis $D\le28$ therefore gives $T\ge m+720$. The square inequality $T+35(m+1)\le9214$ would imply

$$
36m+755\le9214.
$$

At $m=235$, its left side is 9215. Consequently `bound234_of_deficit28` concludes $m\le234$. Its deficit hypothesis is guarded by $235\le m$, so no block-fit claim is required for smaller lengths. Without deficits, the charge at $m=235$ is 9243; the margin above 9214 is 29. A deficit allowance of 28 leaves a strict margin of 1. Allowance 29 would remove that strict numerical contradiction from this estimate.

The third theorem, `deficit26_of_thirteen_exceptions`, gives a sufficient condition for the deficit allowance. For any 39 natural block sums, assume each is at least 23 and at most 13 are below 25. Blocks at least 25 contribute zero deficit; every other block contributes at most 2. Thus

$$
D\le2\cdot13=26\le28.
$$

The proof uses a finite-set filter to count the exceptional blocks and preserves natural truncated subtraction. Applied inside the large-length branch of the preceding theorem, these assumptions suffice for $m\le234$.

The source asserts no geometric or endpoint explanation for these assumptions. In particular, the existing bound of 13 on certain endpoint-related window occurrences has not been connected here to blocks whose six-count sum is below 25. Such a connection would require a separate theorem identifying every exceptional block with a qualifying occurrence. The universal lower floor 23 for these blocks likewise remains a separate hypothesis. The result is a conditional arithmetic target, not an actual-snake exclusion or an unconditional upper bound.
