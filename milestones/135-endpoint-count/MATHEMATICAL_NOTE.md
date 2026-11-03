# Counting low-pair windows in an actual snake

The occurrence theorem and all supporting results in this note passed Lean.
The final three theorems compiled successfully in 14.25 seconds and use only
the recorded standard axioms. No new named mathematical definition is introduced.

## An occurrence bound independent of the path length

The checked result is the following. For any induced path in \(Q_9\),
at most thirty-two fitting windows with canonical transition sequence
\(012032\) satisfy

\[
\alpha_{r+2}+\alpha_{r+4}\le9.
\]

Here \(r\) is the window's starting index and the counts are those used in
the preceding paper and verified endpoint theorem. Each distinct starting
index is counted once. There is no assumption on the parity of the total
path length, and the windows may overlap.

The proof bounds by sixteen the windows assigned to any one endpoint through
the common-neighbour conclusion from milestone 134. A window admitting both
endpoints is assigned to the first endpoint, so the two groups are disjoint.
The result does not assert that either bound can be attained.

## Proof of the sixteen-window estimate

Fix an endpoint, orient the snake from it, and translate it to \(0\). The
first step uses one coordinate. Every assigned window has four alternating
vertices adjacent to an absent unit-coordinate vertex, and that coordinate
differs from the first step's coordinate. The same transformed snake is used
for every assigned window.

Cube parity implies that the window starts are even. Divide their indices
by two and call the resulting finite set \(I\). This division is injective
on the even starts. A start \(r\in I\) covers the four sampled positions
\([r,r+3]\). Write \(A\) for the set of common coordinates used by these
windows and \(a=|A|\). These coordinates belong to the eight coordinates
different from the first step, so \(a\le8\).

Two windows with different common coordinates cannot share two positive
sampled positions. The only common neighbours of two distinct unit-coordinate
vertices are \(0\) and their coordinate-pair vertex. Two shared positive
positions would therefore repeat that pair vertex, contradicting injectivity.
Consequently, if starts \(u<v\) have different common coordinates, then
\(u+3\le v\). The checked interval inequality gives, when \(I\ne\varnothing\),

\[
|I|+2a+1
\le\left|\bigcup_{r\in I}[r,r+3]\right|.
\]

Except at sampled positions zero and one, every covered vertex is a coordinate
pair among the eight available coordinates, with at least one member in
\(A\). There are \(7a-\binom a2\) possible such pairs. Distinct covered
positions represent distinct vertices, and hence

\[
\left|\bigcup_{r\in I}[r,r+3]\right|
\le7a-\binom a2+2.
\]

Combining the inequalities yields

\[
|I|\le1+5a-\binom a2\le16
\qquad(0\le a\le8).
\]

The empty set is immediate. Reversing from the final endpoint sends an
original start \(r\) to \(m-r-6\), an injective transformation on fitting
windows. This completes the same count for either endpoint. Partitioning the
low-pair windows between the two endpoints gives the bound thirty-two.

## Identities needed to improve sixteen to twelve

The stronger written argument from milestone 133 uses consecutive coordinate
pairs to count missing pairs. Let \(F\) be a finite set of missing unordered
pairs, each meeting \(A\), and write \(t=|F|\). For \(u\in A\), let
\(d_u\) count the pairs containing \(u\), and let \(s_u\) count those
whose other coordinate is outside \(A\). These quantities are used throughout
the missing-degree argument. The following identities and inequalities have
passed Lean:

\[
|\{e\in F:u\notin e\}|=t-d_u,
\qquad
\sum_{u\in A}d_u\ge t,
\qquad
\sum_{u\in A}(d_u+s_u)=2t.
\]

If \(t=3\), at most one member of \(A\) has \(s_u=3\). Two such members
would belong to every crossing pair, although a crossing pair has exactly
one member in \(A\).

These results provide the degree arithmetic needed for the exceptional case
\(a=5\), \(t=3\) in the proposed twelve-window proof. The construction of
maximal intervals and their full combination with the actual sequence-length
bound remain pending. Twelve per endpoint and twenty-four in total therefore
retain their status as written estimates with incomplete Lean checking.

## Scope for the length problem

The occurrence estimate restricts how often one problematic local shape can
appear. It supplies no new numerical upper bound on snake length by itself.
Milestone 132 already shows that the current fixed uniform-credit comparison
cannot improve the global bound merely by inserting an occurrence allowance
of at least two. Any later improvement must address its remaining cycle
constraint or provide a stronger comparison.

The recorded interval remains \(191\le a(9)\le235\), with the documented
incomplete independent rebuild of the contributor upper-bound proof.
Optimality and the proposed value \(196\) remain unresolved. The next paper
revision is due at milestone 136.
