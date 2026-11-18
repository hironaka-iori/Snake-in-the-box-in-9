# Round 240: five missing neighbour counts

## Result and verification scope

For an arbitrary binary selection of vertices of \(Q_9\), any 507 of its 512 neighbour counts determine the selection uniquely. If the selection is confined to a known parity side, any 251 of the 256 counts on the opposite side suffice. Thus the minimum number of neighbour counts changed by two different binary selections lies between six and nine.

The proof combines the previously established cube inverse, the written four-count and conditional eight-count results, a complete finite geometric reduction, and exact integer matrix calculations. The current native record reports all 372 relevant matrices nonsingular and no nonzero integer solution for any of their 90,396 ternary right-hand sides. An independent source review agrees with the generated literal equations and independently evaluates the 8,019 residual arithmetic cases after the cofactor argument below.

**Accepted arithmetic:** all 372 Lean matrix modules passed, as recorded in data/matrices-replay.json and the individual source-bound receipts. An independent enumeration of 2,699,004 actual vertex triples recovered the same 372 distance matrices. These are literal matrix theorems. The arbitrary-position geometric cover and the assembly of the five-count theorem on the actual cube remain written/native steps. The assembled actual-cube Lean result currently covers three missing counts.

No longer snake or new global bound on snake length follows from this result.

## Reduction to the five-position equations

Let \(A\) be the adjacency operator of \(Q_9\). For two binary selections agreeing on the observed counts, subtract their indicators to obtain \(f\in\{-1,0,1\}^{512}\). The vector \(Af\) is zero outside the missing positions. The existing inverse is

\[
315f(x)=\sum_{p\in V(Q_9)}\rho(d(x,p))(Af)(p),
\]

where \(\rho(1)=35,\rho(3)=-10,\rho(5)=8,\rho(7)=-16,\rho(9)=128\), and \(\rho\) is zero at even distances.

If at most four counts are missing, use the Round 239 result. If exactly five missing positions have mixed parity, split \(f\) into its two parity restrictions. Each restriction has neighbour sums supported on at most four positions, so both vanish by that result. If no pair of missing positions has distance eight, the Round 239 conditional eight-count theorem applies.

Only five distinct positions of one parity containing a distance-eight pair remain. Write them as \(p_0,\ldots,p_4\), put \(w_i=(Af)(p_i)\), and evaluate the inverse at their antipodes. This gives

\[
Mw=315s,\qquad w\in\mathbb Z^5,\qquad
s_i=f(\overline{p_i})\in\{-1,0,1\}.
\]

The matrix has diagonal 128. Its entries at pairwise distances \(2,4,6,8\) are respectively \(-16,8,-10,35\). The arithmetic result is stronger than required: the integer unknowns \(w_i\) have no imposed size bound, although actual neighbour-sum differences have absolute value at most nine.

## Complete geometric reduction

Translate one endpoint of a distance-eight pair to zero. A coordinate permutation puts the other at the integer vertex 255, with its first eight bits equal to one and ninth bit zero. Every remaining position has even weight.

For each of the first eight coordinates, record the three bits belonging to the remaining three positions. There are eight possible patterns. Their multiplicities are eight nonnegative integers with sum eight, giving

\[
\binom{15}{7}=6435
\]

descriptions. Permuting those first eight coordinates preserves the fixed pair. The ninth bit of each remaining position is uniquely fixed by its even parity. Thus this construction covers every required ordered configuration, without imposing an additional geometric assumption.

The native enumeration rejects repeated positions, leaving 5,160 descriptions. It forms all ten pairwise distances and chooses the least distance tuple under the 120 permutations of the five positions. This leaves 372 metric classes. Equal distance matrices give equal coefficient matrices, so the reduction is valid even if two configurations with the same distances belong to different cube-isometry orbits. The count 372 is a count of distance matrices, not a claimed count of geometric set orbits.

The independent direct-vertex script fixes the same pair \(0,255\) and enumerates all three-element subsets of the other 254 even vertices. Its coverage argument uses actual vertices instead of coordinate multiplicities. Its source has been reviewed. This note does not claim an execution receipt for that separate enumeration until the root worker records one.

## Integer proof and cofactor reduction

For each matrix let \(D=\det M>0\) and \(B=\operatorname{adj}M\). The identity \(BM=DI\) gives

\[
Dw_i=315(Bs)_i.
\]

With \(q=D/\gcd(D,315)\), cancellation of the gcd gives \(q\mid(Bs)_i\). Since each \(s_j\) lies between \(-1\) and \(1\),

\[
|(Bs)_i|\le\sum_j|B_{ij}|.
\]

When \(q\) exceeds this sum, divisibility forces \((Bs)_i=0\), hence \(w_i=0\). This argument is independent of a bound on \(w_i\).

The saved matrices divide into three groups:

| Number of matrices | Rows satisfying the strict inequality | Consequence |
|---:|---:|---|
| 334 | 5 | Every unknown vanishes immediately. |
| 5 | 4 | Four unknowns vanish; the last diagonal equation settles the fifth. |
| 33 | 0 | The finite ternary divisibility calculation is needed. |

For the middle group, the remaining equation is \(128w_i=315s_i\). The left side is even, so the ternary integer \(s_i\) must be zero. Then \(w_i=0\). The five matrix indices are 16, 129, 163, 199, and 251.

For the last group, enumerate \(s\in\{-1,0,1\}^5\). The only vector satisfying every divisibility condition is zero. This is \(33\cdot243=8019\) explicit integer cases. The indices are:

    4, 15, 27, 48, 64, 88, 96, 126, 132, 133, 147,
    152, 153, 156, 193, 204, 218, 243, 252, 258, 268,
    276, 282, 291, 293, 304, 316, 320, 325, 327, 349,
    358, 367.

For any admitted solution in these cases, \(s=0\); multiplying by the adjugate then gives \(Dw=0\), so \(w=0\). Exact determinants in the catalogue range from 15,945,154,560 to 30,919,449,600. The full original arithmetic audit evaluates all \(372\cdot243=90396\) cases rather than relying on the cofactor reduction.

This proves that every exceptional neighbour-sum difference vanishes. The inverse gives \(f=0\), completing the five-count recovery deduction. In the known-parity specialization, all 256 same-side counts are automatically zero; observing 251 opposite-side counts therefore leaves at most five unspecified counts in the full cube.

## Source and kernel boundaries

The file data/five-count-audit.json contains every representative, canonical distance tuple, matrix, determinant, adjugate, and recorded native result. The script scripts/audit_five.py supplies the finite geometric cover and the original exact arithmetic. The script scripts/make_five_proofs.py generates 372 separate Lean modules.

Each generated module has three relevant parts:

1. Five integer identities expressing \(BM=DI\).
2. A finite implication stating that ternary \(s\) satisfying the five determinant divisibilities is zero.
3. A theorem with unrestricted integer unknowns and exactly the five matrix equations, concluding that all five unknowns vanish.

The script scripts/review_five_source.py independently compares every displayed matrix equation, adjugate identity, and divisibility coefficient with the saved data. It checks the ternary hypotheses, integer variable types, zero conclusion, and all 372 adjugate products. It also reproduces the 334/5/33 cofactor partition and independently evaluates all 8,019 cases in the final group. This bounded calculation completed in under one second with no discrepancy. It did not invoke a compiler, solver, or the original enumeration program. Its receipt and source hashes are in logs/five-source-review.json.

The source comparison does not establish kernel acceptance. Conversely, kernel acceptance of the 372 literal algebra statements does not by itself establish that arbitrary five cube positions reach this catalogue. Both boundaries must remain visible in the paper.

## Consequences and remaining question

Every nonzero ternary difference \(f\) has at least six nonzero neighbour sums. A one-vertex difference has exactly nine: its nine neighbours are the only affected positions. Hence

\[
6\le \min_{0\ne f\in\{-1,0,1\}^{512}}|\operatorname{supp}(Af)|\le9.
\]

Every ternary vector is the difference of two binary selections, so this minimum has exactly the stated selection interpretation. The unrestricted six-, seven-, and eight-count questions remain open in this record. By the conditional eight-count theorem, a counterexample in this range must contain a distance-eight pair among its affected counts.

Recovery concerns all binary selections and imposes no connectedness or induced-path condition. It can constrain future construction methods that change a selection while preserving most neighbour counts. It does not guarantee that a reconstructed selection is a snake, or that a longer snake exists.

