# Interval counts for windows assigned to an endpoint

This round checks intermediate results for the stronger endpoint occurrence
estimate. The complete bound of thirty-two low-pair windows from milestone 135
remains the latest checked occurrence theorem. The proposed bound of twenty-four
has not yet been assembled in Lean. Neither result alone lowers the current
global upper bound on snake length.

## Constructing the intervals

Orient and translate the snake from a fixed endpoint, as in the preceding
proof. Divide the even window starts by two. Different common coordinates
force starts to differ by at least three. Sort the starts, and put consecutive
starts in the same block exactly when their gap is at most two. Induction
constructs this decomposition and proves all of the following:

- Each start occurs exactly once, in its original order.
- Every block is nonempty and has one common coordinate.
- Consecutive starts within a block have gap at most two.
- The final start of a block plus three is at most the first start of any later block.

If the first and last starts in a block are \(u\) and \(v\), its four-position
windows cover the whole integer interval \([u,v+3]\). The block contains at
most \(v-u+1\) starts. Two ordered expanded intervals can overlap only at
their common boundary. For \(W\) starts divided into \(k>0\) blocks, with
expanded intervals \(J_1,\ldots,J_k\), the checked inequalities are

\[
W+3k\le\sum_{i=1}^{k}|J_i|,
\qquad
\sum_{i=1}^{k}|J_i|\le\left|\bigcup_{i=1}^{k}J_i\right|+k-1.
\]

Consequently,

\[
W+2k+1\le\left|\bigcup_{i=1}^{k}J_i\right|.
\]

These are constructed blocks of starts. They need not be maximal intervals
of the full sampled path. Two blocks may have the same common coordinate;
the order and overlap estimates still hold. This avoids an unnecessary
maximality argument in the remaining proof.

## Using pairs from the actual snake

Use the notation already needed in the preceding argument. There are eight
coordinates other than the first step's coordinate. Let \(A\) be the common
coordinates used, let \(a=|A|\), and let \(F\) be all absent unordered pairs
among these eight coordinates that meet \(A\). Write \(t=|F|\). For a fixed
\(u\in A\), let \(d_u\) count pairs in \(F\) containing \(u\), and let
\(s_u\) count those whose other coordinate lies outside \(A\).

Consider a sequence of selected pairs \(\{u,b_1\},\ldots,\{u,b_\ell\}\)
at consecutive sampled positions, beginning at path index at least four.
All \(b_i\) must be among the eight coordinates and different from \(u\).
The earlier geometric argument proves that the \(b_i\) are distinct and
that consecutive pairs \(\{b_i,b_{i+1}\}\) are absent from the snake.
The new result instantiates the finite sets directly from this actual snake,
rather than leaving their containment properties as hypotheses.

Let \(U\) be the coordinates \(b\ne u\) for which \(\{u,b\}\) is selected.
The checked run estimate and outside-coordinate identity are

\[
\ell\le\max\{1,|U\setminus A|\}+t-d_u,
\qquad
|U\setminus A|+s_u=8-a.
\]

For the identity, each coordinate outside \(A\) gives exactly one pair
through \(u\). That pair is either selected or absent. Absent choices are
in bijection with the crossing pairs counted by \(s_u\). In particular,
the identity gives the precise outside-coordinate count needed when
\(a=5\) and \(t=3\).

The two checked statements imply

\[
\ell\le\max\{1,8-a-s_u\}+t-d_u.
\]

This displayed combination is an immediate substitution; the saved Lean
modules check its two constituent statements separately. The sequence and
coordinate hypotheses remain explicit. It does not yet sum over all blocks.

## Remaining proof

Apply the constructed blocks to the normalized actual windows, using their
constant common coordinate throughout the covered interval. Remove the
possible initial endpoint and exceptional first pair before applying the
sequence bound. Prove that these exceptional positions are counted only once.
Then combine the selected-pair capacity, missing-pair count, interval overlap
and degree sums from the preceding milestones.

For \(a\le7\), the required inequalities remain

\[
W\le7a-\binom a2-t-2k+\delta,
\qquad
W\le k(5-a+t)-t+1+\delta,
\]

where \(\delta\) records a counted window at the endpoint. The integer
reduction already checked in milestone 133 leaves \(a=k=5\), \(t=3\)
if \(W\ge12+\delta\). The new outside-coordinate identity supplies the
remaining per-block input for this case. The degree sum and the fact that
at most one common coordinate can have three crossing missing pairs were
checked in milestone 135. Their actual-block combination is still pending.
The case \(a=8\) also needs its separate geometric exclusion.

The proposed conclusions of twelve per endpoint and twenty-four in total
retain their pending status. No claim of sharpness or novelty is made.

## Manuscript and verification

Four modules produced eleven successful axiom reports: five for block
construction and coverage, four for interval counting, one for the actual
missing-pair estimate, and one for the outside-coordinate identity. Exact
sources, dependencies, compiler logs and compiled objects are retained.

Paper revision 136 incorporates the completed endpoint and occurrence results,
the odd-length counterexamples, the restricted six-count result, and the
conditional graph comparisons. The proposed stronger count is distinguished
from the completed theorem. No named definition was added. The authors and
complete preamble are unchanged.

The final source checks resolve 238 labels, 266 references and 122 citations
against 54 bibliography entries. Both new printed witnesses are reconstructed
and checked over 20,086 vertex pairs. These checks do not establish PDF layout.
The built-in compiler failed in its Windows helper before TeX execution.
