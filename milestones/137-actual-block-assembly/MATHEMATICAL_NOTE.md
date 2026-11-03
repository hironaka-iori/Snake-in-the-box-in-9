# A checked bound of twenty-four low-pair windows

For any snake in \(Q_9\), the number of distinct fitting canonical
\(012032\) starts satisfying

\[
\alpha_{r+2}+\alpha_{r+4}\le9
\]

is at most twenty-four. This theorem permits overlapping windows and either
path-length parity. The complete actual-snake statement passed Lean.

## Endpoint count

The checked local theorem assigns each such window to an endpoint sharing
an unselected common neighbour with the four alternate window vertices.
Normalize that endpoint once, orient the path from it, and divide its even
window starts by two. There are eight available common coordinates, excluding
the first direction.

Group successive sampled starts whose gaps are at most two. Each block has
one common coordinate, and its expanded interval covers all its windows.
Different expanded intervals overlap in at most one position. Write \(W\)
for the number of starts, \(k\) for the number of blocks, and \(A\) for the
common coordinates used, with \(a=|A|\). Let \(F\) be the absent coordinate
pairs meeting \(A\), and put \(t=|F|\).

The covered union has at least \(W+2k+1\) positions. Apart from sampled
positions zero and one, each is a distinct selected pair meeting \(A\).
There are \(7a-\binom a2\) possible pairs, of which \(t\) are absent.
Thus

\[
W+2k+t\le7a-\binom a2+1. \tag{1}
\]

Remove the exceptional positions from each block. They contribute at most
two positions across the whole list of blocks. If \(\ell\) denotes each
remaining length, then \(\ell\ge2\) and

\[
W+3k\le\sum_{\text{blocks}}\ell+2. \tag{2}
\]

For a block with common coordinate \(u\), let \(d_u\) be its incident
missing degree and \(s_u\) its missing degree to coordinates outside
\(A\). Consecutive regular vertices have the form
\(\{u,b_1\},\ldots,\{u,b_\ell\}\), with distinct \(b_i\) and absent
successive pairs \(\{b_i,b_{i+1}\}\). Exactly \(8-a-s_u\) outside
coordinates give selected pairs through \(u\). The checked sequence bound gives

\[
\ell+d_u\le\max\{1,8-a-s_u\}+t. \tag{3}
\]

For \(a\le7\), summing (3) and using \(\sum_{\text{blocks}}d_u\ge t\)
gives

\[
W+3k+t\le k(8-a+t)+2. \tag{4}
\]

Repeated common coordinates are allowed; their nonnegative degrees only
increase this subtraction. Assuming \(W\ge13\), the checked integer
reduction of (1) and (4), with \(1\le a\le k\), leaves only
\(a=k=5\), \(t=3\). Equality of the number of coordinates and blocks
then implies that each coordinate labels exactly one block.

In this exception, \(\sum_{u\in A}(d_u+s_u)=6\), and at most one
coordinate has \(s_u=3\). Equation (3) gives
\(\sum\ell\le30+1-6=25\). Equation (2) yields \(W+15\le27\),
contradicting \(W\ge13\).

For \(a=8\), (1) and \(W\ge13\) force \(k=8,t=0\). Equation (3)
would give \(\ell\le1\), contradicting \(\ell\ge2\). The empty case
is immediate. Hence each endpoint receives at most twelve windows.

Reversal and halving preserve distinct starts. Assign a window to the initial
endpoint when it qualifies, and otherwise to the final endpoint. The two
groups are disjoint and exhaustive, giving the bound twenty-four.

## Verification and scope

All nine modules passed Lean, including the final normalized, assigned and
total occurrence statements. Twenty-three theorem reports use only the
recorded standard axioms. The final source SHA256 is
6c663ff371f792efe9078f34b3a1bca87334c8e1f5716ef4653e4c544b11eaaf.
An independent reading checked this same source and the supporting chain.
The audit record identifies the exact scope of that review.

The theorem retains the unselected-common-neighbour assignment premise.
The stronger boundary-free count eleven and the broader distance-only
assignment statement are not proved here. Sharpness is not asserted.
The theorem gives no new global upper bound by itself: the surviving
seven-edge cycle in the fixed comparison has no counted event. Its numerical
limitation remains valid even if the allowance were reduced to two.

The next endpoint investigation concerns that seven-edge cycle. A successful
local restriction would address a different obstruction to the length bound.
Finite-model calculations and local solver outcomes must retain their scope
until their interpretation and certificates are checked.
