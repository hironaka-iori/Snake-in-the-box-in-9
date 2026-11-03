# Endpoint consequence of a small pair sum

Let \(p_0,\ldots,p_m\) be a snake in \(Q_9\), with the existing internal
counts \(\alpha_i\). Suppose \(r+6\le m\) and the six directions beginning
at \(r\) have canonical form \(012032\).

## Checked theorem

\[
\alpha_{r+2}+\alpha_{r+4}\le9
\quad\Longrightarrow\quad
\exists e\in\{0,m\},\qquad
d_H(p_{r+2},p_e)=d_H(p_{r+4},p_e)=2.
\]

The same endpoint satisfies both equalities. No parity restriction on
\(m\) or \(r\) is required. In particular, if neither endpoint satisfies
the two equalities, then

\[
\alpha_{r+2}+\alpha_{r+4}\ge10.
\]

This strengthens the previous unconditional local floor eight and the
odd-length floor nine in the stated geometric situation. It does not assert
that every fitting window has pair sum at least ten.

## Proof and verification

Translate the initial window vertex to zero and permute the coordinates.
The normalized window is

\[
(0,1,3,7,6,14,10),
\]

where the integers denote binary cube vertices. The counted centres become
3 and 6. Each count is the number of unselected opposite corners among its
21 allowed squares. Their concatenated lists have 42 occurrences over 37
distinct vertices. The vertices 18,34,66,130 and258 occur in both lists;
their two occurrences must be retained.

Assume the pair sum is at most nine and neither endpoint has distance two
from both centres. Give each vertex its actual path-membership value and
actual endpoint value. Give each counter register the truth value of its
corresponding prefix-count threshold. The selected clauses are then satisfied:

| Requirement | Selected clauses |
|---|---:|
| The seven displayed window vertices belong to the snake | 7 |
| A selected vertex has at most two selected neighbours | 192 |
| A selected degree-one vertex is an endpoint | 32 |
| Ten specified six-vertex cycles cannot be wholly selected | 10 |
| The 42 corner occurrences have sum at most nine | 435 |
| Seven specified vertices are not endpoints | 7 |

The last seven vertices are 0,10,18,34,66,130 and258. Each is at distance two
from both 3 and 6, so the assumed absence of such an endpoint supplies these
clauses. The complete certificate derives a contradiction from the 683
selected clauses. Its 13,299 deductions and 554,859 propagation hints were
independently replayed, exported with an explicit variable bijection, and
checked by Lean in 51 modules. Separate Lean proofs verify the actual-snake
meaning of the clauses and transfer both distances back through the coordinate
map. The corollary follows because the pair sum is an integer.

The original search included two positive endpoint-parity clauses. Neither
occurs in the trimmed proof. The global endpoint-count counter is also unused.
These omissions are checked against the original clause identities, and the
final theorem contains no parity or external contradiction assumption.

The other seven vertices in the common distance-two sphere are
5,15,23,39,71,135 and263. Each is adjacent to the selected internal vertex 7.
Its two path neighbours 3 and 6 already exhaust its allowed selected neighbours,
so none of those seven vertices can be selected. This explains the smaller
set used by the certificate without changing the stated geometric conclusion.

The semantic compilation required two repairs. Both failed attempts, their
sources and logs are preserved. The corrected compilation and final
assembly passed. All final theorem reports use only propext, Classical.choice
and Quot.sound. No missing proof or native-decision axiom occurs in the final
statements. This is a computer-assisted proof of the displayed local theorem;
no claim of historical novelty is made.

## Why a uniform credit remains insufficient

In the fixed first-profile graph from milestone 131, the four-edge cycle has
mean 488 and two qualifying suffix occurrences. Giving each such occurrence
credit \(C\ge0\) bounds any resulting minimum mean by \(488+C/2\).
The other saved seven-edge cycle has no such occurrence; under the same
first-profile weights its mean is \(3453/7\). Thus

\[
\mu\le488+C/2,\qquad \mu\le3453/7.
\]

For a nonnegative mean \(\mu\) and potential range \(R\), the existing comparison with an
allowance of two occurrences is

\[
\frac{1098960+8\mu+2C+R}{4200+\mu}>235.
\]

Lean checks this conditional arithmetic and its extension to every allowance
at least two. The cycle data and the charging formula remain explicit premises;
this assertion does not turn the finite graph into a global snake bound.
The independent written calculation gives the stronger gap

\[
\frac{1098960+8\mu+2C+R}{4200+\mu}
\ge235+\frac{37}{32853}.
\]

Indeed, the numerator of the difference from 235 equals

\[
(2C-4\mu+1952)+223(3453/7-\mu)+R+37/7\ge37/7,
\]

and \(0<4200+\mu\le32853/7\). The sharper numerical gap is written and
independently reviewed; the current Lean statements check the strict
inequality and the allowance extension.

## What remains open

The endpoint theorem restricts repeated low-pair windows to the geometry near
the actual endpoints. The next useful task is to count their possible
arrangements, including overlap between windows. The earlier bound thirteen
uses the intersection of the distance-two spheres of BOTH endpoints. The new
existence conclusion does not justify applying that bound separately to each
endpoint or asserting an allowance of 26.

Even a new occurrence bound must be checked against the competing seven-edge
cycle and the potential range. The uniform-credit calculation above explains
why endpoint proximity alone does not yet establish an improved upper bound.

The maintained global interval remains 191–235, with the existing independent
rebuild limitation. The value 196 and optimality remain unresolved. Existing
notation is retained; no additional named mathematical quantity is needed.
