# Shared rejection covers and history transport

Let \(D=\{1,\ldots,6\}^{6}\) be the encoded count domain. The symbol six
represents the previously defined interval of actual counts; it is not an
assertion that an actual count equals six. A context consists of a direction
ID \(d\in\{0,\ldots,504\}\) and a history ID
\(q\in\{0,\ldots,74\}\). Write \(K_{d,q}\subseteq D\) for the vectors
passing numeric retention in that context.

## Shared rejection covers

A rejection cover for a membership set \(C\subseteq D\) is an ordered list
of count boxes \(\mathcal B=(B_0,\ldots,B_{s-1})\) such that

\[
D\subseteq C\cup\bigcup_{i=0}^{s-1}B_i.
\]

Suppose each box has a valid rejection witness in context \((d,q)\).
The rejection-witness theorem gives
\(K_{d,q}\cap B_i=\varnothing\) for every \(i\). Therefore

\[
K_{d,q}\subseteq C.
\]

Indeed, a retained vector belongs either to \(C\) or to one of the boxes,
and its rejection witnesses exclude the latter possibility. This argument
requires coverage and sound witnesses. It does not require that the boxes be
disjoint or that their number be minimal.

A cover is *shared* by several contexts when the same ordered boxes are used
and every context supplies an aligned list of valid witnesses. The geometric
coverage equation can then be checked once for the whole class. Witness
validity remains a statement about its particular context. Order is part of
the certificate because coverage-tree leaves refer to box positions.

The generic shared-cover assembly is checked in Lean. It joins a box list
and an equally long witness list, proves that the first components recover
the complete box list, and applies the coverage theorem. Equality of lengths
prevents silently dropping boxes when the lists are paired.

## History-free witnesses

A witness is *history-free* if it uses a reference, short-rule or interval
exclusion. These three constructors inspect the direction and count box,
while the outer validity test only requires the history ID to lie below 75.
Consequently, for any two history IDs \(q_0,q<75\), validity at \(q_0\)
implies validity at \(q\), with the direction and box fixed.

The same implication holds for a list consisting entirely of history-free
witnesses. Thus one validity check at history zero can be reused across
the applicable histories of that direction. A separately checked history
witness may be placed before or after this base list. The order used by a
concrete geometric certificate must still be preserved.

This transport statement does not assert that two contexts have identical
retained sets. A history exclusion can remove additional vectors. It only
transports the specified history-free rejection witnesses.

## Exact computational instances

The 791 compatible contexts divide into 127 membership classes. The saved
common covers contain 82,659 class-box occurrences. Expanding their use
across contexts requires 543,827 box-witness occurrences. Every occurrence
has been materialized and checked computationally against an original rule.
The data compress to 211 aligned witness lists using 4,387 distinct witness
constructors. All class IDs and box orders agree with milestone 88.

There are 788 history-free contexts. The other three have their sole history
witness at position zero:

| Direction | History | Membership class | History-rule index |
| ---: | ---: | ---: | ---: |
| 177 | 43 | 85 | 0 |
| 177 | 70 | 85 | 2 |
| 180 | 68 | 89 | 1 |

The first two witness lists differ only at that position. The nonhistory
occurrences correspond to 356,592 distinct direction/geometry pairs, so
187,232 repeated occurrences can potentially use the checked transport
argument. These counts describe the generated data; they do not substitute
for concrete Lean validity equations.

All 127 geometric coverage trees have also been generated. They have
152,643 distinct nodes within their respective class certificates and
1,499,755 expanded node visits. An independent pointwise replay checks every
class against all \(6^6\) codes, for 5,925,312 checks. Each class's successful
Lean receipt, when present, records its stronger proof status separately.

## Checking equivalent representations

The array-based coverage checker uses the same cases, prefix test and
six-way branching as the original list-based checker. Only indexed box
access changes. Lean proves their equality for every diagram, box array,
fuel value, prefix, root and certificate. An array-check equation therefore
implies the original list-check equation. A concrete timing experiment is
recorded separately; the equivalence theorem itself establishes no runtime
claim.

A second representation stores the table in a binary tree. Each internal node
records the number of leaves in its left subtree. Lookup compares the requested
index with that number and enters one child, adjusting the index on the right.
The checked validity condition requires every recorded split size to be correct.
Lean proves that lookup then agrees with the flattened list at every natural
index, with the same default outside its range.

For the generated literals, the graph table has depth twelve, and box tables
have depth nine or ten. Their order and split sizes were independently checked
computationally. Lean also checks the graph table's validity and exact contents.
Class 1's balanced coverage equation passes, and the generic lookup equivalence
derives the original list-based coverage equation. The sequential full-class
run is recorded separately; one checked class does not certify all 127.

## Remaining mathematical obligations

The final graph argument still requires the concrete geometric equations,
all context-specific witness equations, and the assignment of each compatible
context to its recorded class. Diagram membership must then imply membership
in the saved full-key rows with the stated endpoint columns. The two
reference-catalogue premises, local credit interpretation, unfinished share
lemmas and complete potential replay retain their previous status.

The maintained interval remains 191 through 235 edges, with 234 conditional.
The 235 upper bound uses the inspected contributor theorem and saved audit;
this milestone does not provide an independent rebuild or a smaller bound.
