Compilation update: the final saved source passed the guarded Lean compiler. Accepted receipts are in data/. Preparation and repair status below is historical.

# Exact inverse of Q9 adjacency between parity classes

Status: source preparation only. No compiler, solver, or tests were run.

The separate source lean/AdjacencyInverse236.lean leaves ExchangeBalance236.lean unchanged. It contains two exported statements: the five integer recurrence equations and a general finite-list reconstruction theorem. The cube-distance interpretation remains a written argument.

## Elementary derivation

Write the adjacency matrix with minority vertices as rows and majority vertices as columns. For an integer change z on the majority class, let

\[
b(v)=\sum_{t\sim v}z(t).
\]

Fix majority vertices a and t at even distance k. Of the nine minority neighbours v of t, exactly k have distance k-1 from a and exactly 9-k have distance k+1. This follows by distinguishing whether the flipped coordinate is one where a and t differ.

Give opposite-parity distances 1,3,5,7,9 the respective weights 35,-10,8,-16,128, and give all other distances weight zero. The coefficient of z(t) in the weighted sum of b(v) is therefore

\[
k\,c(k-1)+(9-k)c(k+1).
\]

The five possible even distances give

\[
\begin{aligned}
9(35)&=315,\\
2(35)+7(-10)&=0,\\
4(-10)+5(8)&=0,\\
6(8)+3(-16)&=0,\\
8(-16)+128&=0.
\end{aligned}
\]

Expanding the finite sums hence gives

\[
\sum_v c(\operatorname{dist}(a,v))b(v)=315z(a).
\]

The weight function depends only on distance, but the change z and the observations b are completely arbitrary. No symmetry of a candidate snake, its changed vertices, or its endpoints is assumed. The recurrence constructs an integer numerator for the inverse; the inverse itself has these coefficients divided by 315.

This is an elementary matrix-inverse calculation and a linear recombination of the neighbour equations. No novelty or stronger feasible-set claim is made.

## What the Lean source establishes

The distance_recurrence statement checks each of the five integer equations by kernel computation. It does not yet prove the cube fact that the relevant neighbour multiplicities are k and 9-k.

The reconstruct statement uses arbitrary finite row and column lists, an integer incidence array, integer coefficients, and integer observations. It assumes that the columns have no repetitions, that the reconstructed column is present, that each observation is the stated incidence sum, and that the coefficient array is a scaled left inverse on those columns. It proves reconstruction by expanding the observations, swapping the two finite sums, and evaluating the resulting single nonzero term. It does not assume the desired reconstruction equality.

To obtain the full Q9 theorem in Lean, the remaining bridge is a complete, duplicate-free enumeration of both parity classes, cube adjacency and distance, the k and 9-k neighbour counts, and the resulting left-inverse identity with scale 315. The two exports have only been prepared, and neither is claimed checked until the parent compiler run succeeds.

## Application and limitations for exchanges

For the 191-edge seed and 192-edge target, z is the new majority indicator minus the old majority indicator. Its values belong to {-1,0,1}; its sum is one because the majority class grows from 96 to 97.

At a retained minority vertex, the new path degree is two, so the previous exchange-balance argument gives b(v)=e_P(v). Thus b is zero at every retained seed-internal minority vertex, and is one at the old minority endpoint if that endpoint is retained. At other minority vertices the observation is not fixed by these retained-vertex equations. It is still a neighbour sum and cannot be treated as an arbitrary unbounded integer.

Summing over every minority vertex counts every majority change nine times:

\[
\sum_v b(v)=9\sum_a z(a)=9.
\]

Consequently the observations on the other minority vertices sum to eight if the old minority endpoint is retained, and nine otherwise. The written proof uses only the nine neighbours of each majority vertex. No additional finite-sum export is supplied for this companion identity.

The inverse imposes exact reconstruction, divisibility by 315, and the selection restrictions

\[
\sum_v c(\operatorname{dist}(a,v))b(v)\in\{-315,0,315\}.
\]

The possible signs are further restricted by old membership: a vertex already in the old majority class has z(a) in {-1,0}, and one outside it has z(a) in {0,1}. These are useful requirements for a search expressed in terms of observations. They are already consequences of the full integer degree model with the original selection variables.

Only fixing the retained observations leaves many unknowns. With r minority deletions, there are 160+r minority vertices outside the retained 96-r vertices. The inverse alone therefore does not determine a candidate from its old endpoint data.

For an actual candidate, an inserted minority vertex has b(v) between -7 and 2 because its new degree is two and its old neighbour count is between zero and nine. A deleted seed-internal minority vertex has b(v) between -2 and 7; a deleted seed endpoint has b(v) between -1 and 8. A minority vertex unselected in both paths has b(v) between -9 and 9. These bounds follow directly from selection status and should be retained if observations become search variables.

The inverse does not impose connectivity, remove the disjoint-cycle issue, prove that a target exists, or establish any exclusion. Its immediate use is a different exact coordinate system and a way to detect inconsistent proposed neighbour changes. Any computational advantage requires separate evidence.

## First compiler attempt and source repair

The parent ran the first compiler attempt. It failed at three simplification steps: the zero-row case of sum interchange, a sum of a constant-zero list, and a reflexive conditional in the single-term sum. The log and original source are preserved in logs/AdjacencyInverse236-1794930069136011700/compiler.log and source.lean.txt. The failed source has SHA-256 2bc43e00f0162c0211bcbb32d560c29564701b49df3c8b6ce12915dcc5cf535e.

The repair adds an explicit induction for the sum of a constant-zero list, uses it in both zero-sum obligations, and uses ordinary simplification for the reflexive conditional. The statements and mathematical hypotheses are unchanged. No compiler was run during this repair. In particular, the first failed reconstruction report contains sorryAx and must not be treated as accepted.
