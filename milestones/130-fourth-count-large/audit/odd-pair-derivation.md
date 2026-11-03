# Pair equality requires even length and an even start

Lean checks the following statements for an actual induced path
\(p_0,\ldots,p_m\) in \(Q_9\). Let \(r+6\le m\), and suppose the six
directions starting at \(r\) have canonical word \(012032\). Then

\[
\alpha_{r+2}+\alpha_{r+4}=8
\quad\Longrightarrow\quad
m\equiv0\pmod2\ \text{and}\ r\equiv0\pmod2.
\]

Combining this with the proved pair lower bound eight gives

\[
\alpha_{r+2}+\alpha_{r+4}\ge9
\quad\text{if }m\equiv1\pmod2\ \text{or }r\equiv1\pmod2.
\]

In particular, every fitting canonical \(012032\) window in a snake of
235 edges satisfies the pair lower bound nine. The start index is the
existing zero-based path index: the relevant centres occur at positions
\(r+2\) and \(r+4\).

## Argument

The completed endpoint theorem states that pair equality places both centres
at Hamming distance two from both endpoints. Vertices at Hamming distance
two have the same parity of the number of one coordinates. Thus the centre
at position \(r+2\) has the same parity as \(p_0\), which forces \(r+2\)
and hence \(r\) to be even. Both endpoints also have the same parity, which
forces \(m\) to be even because each path edge reverses parity.

The existing pair theorem gives a sum at least eight. If either length or
start is odd, the equality case is impossible. The sum is an integer, so it
is at least nine. The specialization to 235 uses its odd parity directly.

The proof uses a generic list induction showing that the parity of an XOR
count is the parity of the sum of the two counts. This yields the XOR rule
for vertex parity and then the distance-two parity statement. It does not
enumerate triples of cube vertices. No new mathematical definition is
introduced.

## Checked statements and evidence

`OddPair130` passed eight printed axiom reports in 77.828 seconds:

- parity of a generic XOR count;
- parity of the XOR of two vertices;
- equality of vertex parity at Hamming distance two;
- even length and start forced by actual pair equality;
- pair lower bound nine when the length or start is odd;
- its odd-length and odd-start specializations;
- its length-235 specialization.

Every report contains only a subset of `propext`, `Classical.choice` and
`Quot.sound`. The source contains no omitted proof or native-decide step.

The earlier `DfsParity` verification recorded source and theorem audits but
did not bind the current compiled object to that invocation. An exact byte
copy of `work/final_lean/DfsParity.lean` was therefore rebuilt in this
milestone. Its four existing reports passed in 24.843 seconds. The new
proof resolves that rebuilt object first. Its endpoint and pair objects
match the hashes in the completed milestone-122 audit saved in milestone 129.

Both compiler checks used the required fresh resource gate and a bounded
600-second allowance. Source snapshots, compiler logs, checker snapshots,
resolved import hashes and dependency pins match the successful receipts.
No failed compiler attempt occurred for these two checks.

The stable receipts are `data/independent-parity-dependency-audit.json` and
`data/independent-odd-pair-audit.json`. The combined record is
`data/odd-pair-verification.json`.

## Scope

Even length and even start are necessary for equality; the result does not
assert their sufficiency. The strengthened pair inequality applies to the
specified actual windows. Its use in a global bound still requires the
corresponding counting or graph argument, with the window indices matched
correctly. No new numerical upper bound for the longest snake is claimed.

## Fixed evidence hashes

| Evidence | SHA256 |
|---|---|
| DfsParity source | `c92b3421c70fc530cd48b4e02add01b07a44693b5f8b2669223cc5db62e01a0a` |
| DfsParity object | `4315db5e773d6344d0ce0961044f8158ee070e10e32456234e25cba81b385483` |
| DfsParity receipt | `5f8b67a27a12ab58f38103f685a615a1439d2deec0a98c7e8a97a84a619b6759` |
| OddPair130 source | `ac5ece213598a89df242f46e5702b9b6b84cd443a9651e0bcc180269addc9fee` |
| OddPair130 object | `3cbcbf5b092f02e898d5742ccf58715d80b7b7252a916e7d53ef0ee6ed867301` |
| OddPair130 receipt | `e849bb0bfd2c7870f83398feb855f0aab03a22f786a1c54905e5900ff51244b8` |

Combined verification SHA256: `06b2eac79854bf65ba839bf49c56965df6dc888dc5c5804f67c11d15af26e799`.
