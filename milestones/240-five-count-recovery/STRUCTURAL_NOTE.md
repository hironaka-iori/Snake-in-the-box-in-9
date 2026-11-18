# Round 240 structural challenge: distance-eight support graphs

This note records written deductions and a limitation of extending the five-position matrix method. It supplies no universal six-, seven- or eight-count recovery theorem. No novelty claim is made. The explicit finite Lean source named below subsequently passed the guarded compiler, with eight accepted axiom reports in data/EightCubeObstruction240-audit.json. Its scope remains narrower than the written structural classifications.

## 1. Distance eight gives the folded cube of order nine

Let \(J=(1,\ldots,1)\in\mathbb F_2^9\) and \(g_i=J+e_i\), for \(0\le i<9\). Two even-weight vertices are at distance eight exactly when their difference is one of these nine generators. For a subset \(I\subseteq\{0,\ldots,8\}\),

\[
\sum_{i\in I}g_i=(|I|\bmod2)J+\sum_{i\in I}e_i.
\]

If this sum is zero and \(|I|\) is even, then \(I\) is empty. If it is zero and \(|I|\) is odd, then \(I\) contains all nine indices. Thus the only nonempty relation among distinct generators uses all nine. Any eight generators are independent and span the even-weight subspace.

In an odd closed walk, retain the generators used an odd number of times. Their sum is zero and their number is odd, so all nine must occur. Every odd closed walk therefore has length at least nine. Traversing each generator once produces a simple nine-cycle: an earlier repeated vertex would give a nonempty proper relation. The distance-eight graph consequently has odd girth nine. Every induced subgraph on at most eight vertices is bipartite. Translation gives the same conclusion on the odd parity side.

This graph is the known folded cube of order nine. The unique generator relation and odd-girth property are stated in Section 2, printed page 7, of Mancinska, Pivotto, Roberson and Royle, *Cores of Cubelike Graphs*, European Journal of Combinatorics 87 (2020), 103092; [author manuscript](https://backend.orbit.dtu.dk/ws/files/256075181/1808.02051.pdf), [DOI](https://doi.org/10.1016/j.ejc.2020.103092). The elementary argument above identifies the graph needed here.

## 2. A stronger reduction for connected components

A connected set of \(k\le8\) positions has a spanning tree using at most \(k-1\le7\) distinct generator labels. Call this label set \(I\). After translating its root to zero, every position is a sum of generators from \(I\). Independence makes these sums unique, so they give ordinary binary coordinates in \(Q_{|I|}\).

An additional distance-eight edge cannot use a label outside \(I\): that would give a relation involving at most \(|I|+1\le8\) distinct generators. Thus the entire induced distance-eight graph embeds as an induced subgraph of an ordinary cube of dimension at most seven.

The original nine-dimensional distance is also retained. If two lifted vertices differ in \(t\) generator coordinates, then

\[
d_{Q_9}=\begin{cases}t,&t\text{ even},\\9-t,&t\text{ odd}.\end{cases}
\]

This permits classification of connected small supports by their generator-labelled cube configurations. Disconnected components still have arbitrary relative translations; their cross-component matrix entries are even, with absolute value at most sixteen, and do not vanish in general.

## 3. The matrix and the required amplitude restriction

Let \(f:Q_9\to\{-1,0,1\}\) be a difference of binary selections and let \(Af\) be its nine-neighbour sum. If \(Af\) is supported at same-parity positions \(p_i\), write \(w_i=Af(p_i)\). The inverse at their antipodes gives

\[
Hw=315s,\qquad s_i\in\{-1,0,1\},\qquad |w_i|\le9,
\]

where the diagonal of \(H\) is 128 and its off-diagonal entries at distances 2,4,6,8 are respectively \(-16,8,-10,35\). Bipartiteness applies to the graph of odd coefficients 35. The full matrix remains dense, with additional even couplings. Bipartiteness by itself therefore does not remove these couplings.

## 4. Eight points where unbounded integer exclusion fails

Take all sums of \(g_0,g_1,g_2\), in binary-subset order:

\[
(0,510,509,3,507,5,6,504).
\]

Their distance-eight graph is \(Q_3\). Put

\[
\chi=(1,-1,-1,1,-1,1,1,-1).
\]

At generator-cube distances 0,1,2,3 the matrix coefficients are respectively 128,35,-16,-10. Consequently

\[
H\chi=(128-3\cdot35+3(-16)-(-10))\chi=-15\chi.
\]

Thus

\[
w=21\chi,\qquad s=-\chi
\]

is a nonzero integer solution of \(Hw=315s\), with ternary right-hand side. It rules out a proposed unbounded-integer exclusion for every eight-position antipodal matrix. Every amplitude is 21, exceeding the necessary bound nine, so it is not a binary-selection recovery counterexample.

`lean/EightCubeObstruction240.lean` checks only this explicit finite statement: distinct even vertices below 512, the nine-bit distance computation, eigenvalue -15, the displayed matrix solution, ternary right-hand side and amplitude 21 greater than nine. It does not encode the written general cube recovery argument.

## 5. Complete bounded exclusion for these eight points

In fact the only integer solutions of this matrix equation with ternary \(s\) are

\[
(s,w)=(0,0),\quad(\chi,-21\chi),\quad(-\chi,21\chi).
\]

Here is a short written proof. For each character \(\eta\) of \(\mathbb F_2^3\), set

\[
S_\eta=\sum_xs(x)\eta(x),\qquad W_\eta=\sum_xw(x)\eta(x).
\]

Character orthogonality diagonalizes the distance-dependent matrix. Its eigenvalues, by character weight 0,1,2,3, are

\[
175,\qquad189,\qquad99,\qquad-15.
\]

All are nonzero. For a weight-two character,

\[
99W_\eta=315S_\eta\quad\Longrightarrow\quad11\mid S_\eta.
\]

Since \(|S_\eta|\le8\), every weight-two sum vanishes. Every character sum has the same parity as \(S_0\). Thus \(S_0\) is even. The weight-zero equation gives \(5\mid S_0\); together with \(|S_0|\le8\), this gives \(S_0=0\).

The weight-one equations give \(3\mid S_\eta\). Walsh inversion, reduced modulo three, therefore gives

\[
8s(x)\equiv S_\chi\chi(x)\pmod3.
\]

Because eight is invertible modulo three, \(s(x)\) has the same residue as \(a\chi(x)\) for one fixed \(a\in\{-1,0,1\}\). Ternary integers are unique representatives modulo three, so \(s=a\chi\) exactly. Invertibility and \(H\chi=-15\chi\) give \(w=-21a\chi\). Requiring \(|w_i|\le9\) forces \(a=0\).

This classification is a written proof. The explicit Lean obstruction file checks the displayed oversized witness, not this Walsh classification.

## 6. Another complete family: an entire distance-eight star

Suppose the whole same-parity missing-position set is one centre and \(r\) distance-eight neighbours, with \(1\le r\le7\). After translation these are zero and \(r\) distinct generators. Every leaf pair is at distance two.

Subtracting two leaf equations gives

\[
144(y-z)=315(t-u),\qquad t,u\in\{-1,0,1\}.
\]

Equivalently \(16(y-z)=35(t-u)\). Since \(|t-u|\le2\), divisibility by sixteen forces \(t=u\) and \(y=z\). Thus all leaf unknowns have one value \(y\), and all their right-hand sides have one ternary value \(t\). With centre values \(x,s\), the remaining equations are

\[
128x+35r y=315s,\qquad35x+(144-16r)y=315t.
\]

Their determinant is \(D_r=18432-3273r\), and elimination gives

\[
D_r y=315(128t-35s).
\]

The positive reduced divisors \(|D_r|/\gcd(|D_r|,315)\), for \(r=1,\ldots,7\), are

\[
5053,566,957,356,689,134,1493.
\]

Each must divide \(128t-35s\), which lies in

\[
\{0,\pm35,\pm93,\pm128,\pm163\}.
\]

Only zero is divisible by any listed divisor; for 134 the only possible nonzero multiples in the displayed range would be \(\pm134\), which are absent. Hence \(128t=35s\). Ternarity gives \(s=t=0\), and the nonzero determinant gives \(x=y=0\).

This excludes every entire-support star of at most eight positions, even without amplitude bounds. It does not apply directly to a star component coupled to other components. This family deduction is written and has no new Lean assembly in this round.

## 7. Why a universal dimension-n claim is false

On \(Q_2\), define \(h(00)=1\), \(h(11)=-1\), and zero elsewhere. Its neighbour sum is zero. Tensoring \(r\) copies gives a ternary function on \(Q_{2r}\) with support \(2^r\) and zero neighbour sum. Extend it to one face of \(Q_{2r+1}\), assigning zero to the other face. The neighbour sum vanishes on the original face and is exactly the tensor product on the other face. Its support has size \(2^r\).

For \(Q_3\), the selection difference supported at \(0,3\), with signs \(+,-\), has neighbour-sum support \(\{4,7\}\), of size two. For \(Q_5\), signs \(+,-,-,+\) at \(0,3,12,15\) give neighbour-sum support \(\{16,19,28,31\}\), of size four. Both contradict a blanket lower bound equal to the dimension. In \(Q_9\), the same construction has support sixteen and therefore does not decide the proposed minimum nine.

## Remaining gap and useful direction

The general six-through-eight-position question remains unresolved here. A valid continuation must preserve the bound \(|w_i|\le9\) or use additional inverse evaluations beyond the antipodes; the eight-point cube demonstrates why the unbounded five-matrix statement cannot be extrapolated.

A structural continuation can classify connected small generator-cube configurations and exploit their row symmetries or character decomposition. It must also cover disconnected configurations with nonzero even cross-component couplings. The folded-cube odd-girth result narrows the geometry, while the star and three-cube arguments show two ways to use more than bipartiteness. None of these arguments changes the snake-length interval or proves a new construction.
