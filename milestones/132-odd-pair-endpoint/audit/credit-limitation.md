# Independent check of the uniform pair-nine credit limitation

Result: `PASS_TWO_CYCLES_AND_UNIFORM_CREDIT_LIMITATION`. The two saved cycles and the proposed comparison arithmetic were checked independently. No graph search, Lean compilation, or solver was run. Frozen milestone131 files were left unchanged.

The original source weight array was loaded once, using 19,788,032 bytes, and its full hash matched the saved source model. Its eleven selected weights were combined with the first profile's count-free floors and independently reconstructed shared bonuses. Directions, counts and adjacency were reused from the milestone131 rows already independently checked against all original arrays; the saved result hash was verified again.

The four-edge cycle has first-profile weights

\[
(480,496,360,616),\qquad \text{sum}=1952,\qquad \text{mean}=488.
\]

Its exact pair-sum-nine suffix events occur on edges 2222328 and 2220858. The other two pair matches are prefix placements of the same consecutive windows and are not counted a second time. Thus a uniform added credit \(C\) per suffix event gives cycle mean \(488+C/2\).

The seven-edge cycle, evaluated under the first profile's weights, has

\[
(732,376,366,376,616,251,736),\qquad
\text{sum}=3453,\qquad \text{mean}=\frac{3453}{7}.
\]

It has no canonical \(012032\) match in either placement, so this uniform credit leaves all seven weights unchanged. Both cycles remain closed in the same retained graph. Consequently its minimum mean satisfies

\[
\mu\leq 488+\frac C2,
\qquad
\mu\leq\frac{3453}{7}.
\]

Assume \(C\geq0\), \(R\geq0\), \(\mu\geq0\), and the proposed charge comparison permits two events, giving

\[
\frac{1098960+8\mu+2C+R}{4200+\mu}.
\]

The numerator minus 235 times the denominator is exactly

\[
\begin{aligned}
111960-227\mu+2C+R
&=(2C-4\mu+1952)
  +223\left(\frac{3453}{7}-\mu\right)+R+\frac{37}{7}\\
&\geq\frac{37}{7}.
\end{aligned}
\]

Each parenthesized term is nonnegative by the two cycle caps. Since the positive denominator is at most \(32853/7\), the stronger uniform conclusion is

\[
\frac{1098960+8\mu+2C+R}{4200+\mu}
\geq235+\frac{37}{32853}
=\frac{7720492}{32853}>235.
\]

The arithmetic relaxation attains equality at \(\mu=3453/7\), \(C=74/7\), and \(R=0\). This equality statement concerns only the displayed constraints; it does not assert that the graph has a potential of range zero with those parameters.

Therefore the fixed uniform-credit rule, even with an allowance of only two events, cannot make this comparison reach 235 or below. The calculation leaves the proposed endpoint property unresolved. Nonuniform credits, additional state restrictions or edge deletions, and different charge comparisons fall outside this result. It supplies no global impossibility statement and no new actual-snake upper bound. The inherited model hypotheses and graph-to-snake assembly remain pending as recorded in milestone131. The coordinator's separate Lean arithmetic check is outside this review.

The audit completed without a failed assertion. The saved JSON contains the reconstructed edge-by-edge weights, event positions, exact rational arithmetic, assumptions, limitations and input hashes.

- `data/credit-limitation.json`: SHA256 `5c38b530315591a5f2db4d0043c66cd167e98feeeee74de14144d9a85c231743`.
- `audit/check_credit_limitation.py`: SHA256 `03be5ed5946b175171e962322f53d9ffb87927ffab324afdf6f84db089121c30`.
