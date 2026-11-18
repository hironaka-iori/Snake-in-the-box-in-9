# Three missing neighbour counts: independent mathematical review

## Arithmetic statement

Let

\[
M=\begin{pmatrix}128&a&b\\a&128&c\\b&c&128\end{pmatrix},
\qquad a,b,c\in\{0,35,-10,8,-16\}.
\]

If \(x,y,z\) are integers and

\[
M(x,y,z)^{\mathsf T}=315(s,t,u)^{\mathsf T},
\qquad s,t,u\in\{-1,0,1\},
\]

then \(x=y=z=0\). No bound on the three unknown integers is needed. The argument covers all 125 coefficient triples, including triples that cannot arise from cube distances.

The only odd coefficient is 35. Permuting rows and the corresponding columns reduces the proof to four cases according to how many of a,b,c equal 35.

### No coefficient equals 35

Every left side is even, so s=t=u=0. If m is the largest absolute value among x,y,z, a row attaining m gives \(128m\le32m\), because the two off-diagonal absolute values are at most 16. Thus m=0.

### Exactly one coefficient equals 35

Put a=35, so b,c are even and have absolute value at most 16. The third equation is even, forcing u=0. Let \(m=\max(|x|,|y|)\). The third equation gives

\[
128|z|\le16(|x|+|y|)\le32m.
\]

One of the first two rows attains m, and hence

\[
128m\le315+35m+16|z|\le315+39m.
\]

Therefore \(89m\le315\), so m is at most 3. The third-row bound then forces z=0. Subtracting the first two rows gives

\[
93(x-y)=315(s-t),\qquad31(x-y)=105(s-t).
\]

Since 31 and 105 are coprime and \(|s-t|\le2\), s=t and x=y. The first row becomes \(163x=315s\). Coprimality and \(|s|\le1\) force s=x=0, and therefore y=0.

### Exactly two coefficients equal 35

Put a=b=35, with \(c\in\{0,-10,8,-16\}\). Subtracting the last two rows gives

\[
(128-c)(y-z)=315(t-u).
\]

The possible coefficients 128-c are 128, 138, 120 and 144. None divides 315 or 630. Since t-u is one of -2,-1,0,1,2, it follows that t=u and y=z.

The remaining equations are

\[
128x+70y=315s,\qquad35x+(128+c)y=315t.
\]

Eliminating x gives

\[
D y=315(128t-35s),\qquad D=128(128+c)-2450.
\]

The relevant exact integers are:

| c | D | gcd(D,315) | D/gcd(D,315) |
|---:|---:|---:|---:|
| 0 | 13934 | 1 | 13934 |
| -10 | 12654 | 9 | 1406 |
| 8 | 14958 | 9 | 1662 |
| -16 | 11886 | 21 | 566 |

Thus the last column divides 128t-35s. Its absolute value is at most 163, smaller than every entry in the last column, so it is zero. Since \(|s|\le1\), the identity \(128t=35s\) forces t=s=0. Consequently y=x=z=0.

### All three coefficients equal 35

The same row-subtraction argument with coefficient 93 forces s=t=u and x=y=z. Each row is then \(198x=315s\), or \(22x=35s\). Hence s=x=0.

This completes the arithmetic proof without enumerating 3375 right-hand-side cases. A Lean implementation can instead classify by the locations of coefficient 35 and use the four small residual coefficient cases. The existing 237 two-coefficient lemma is private; a new proof may either expose a reusable lemma within its own module or repeat the short coefficient-35 argument above.

## Consequence on the actual cube

Let A be the Q9 adjacency operator. Suppose an integer function f satisfies \(-1\le f(v)\le1\), and Af vanishes outside three distinct vertices p,q,r. Set x=Af(p), y=Af(q), z=Af(r). Apply the checked round-237 inverse at the antipodes of p,q,r. The diagonal coefficients are 128, the off-diagonal coefficients belong to the stated five-element set, and the right sides are 315 times ternary values of f. The arithmetic statement forces x=y=z=0. The inverse then gives f=0.

Therefore, as a written theorem, neighbour counts at any 509 of the 512 vertices determine a binary selection uniquely. If the selection is confined to a known parity side, any 253 of the 256 opposite-side counts suffice, since all same-side counts are already zero. These are mathematical deductions; the parent worker is responsible for the new Lean assembly and its compiler receipt.

Actual cube geometry is stronger than the arithmetic lemma requires. A coefficient 35 corresponds to distance eight between the missing vertices. Two distance-eight neighbours of one vertex have distance two from each other, so the exactly-two-35 case can only have c=-16. Three pairwise distance-eight vertices cannot occur in Q9. No reliance on those additional geometric facts is necessary.

## Minimum support question

For nonzero ternary f, the deduction above gives \(|\operatorname{supp}(Af)|\ge4\). A function supported at one vertex has Af supported at its nine neighbours, giving an example with support size 9. Thus the currently justified range for the minimum support is 4 through 9.

The conjectural minimum 9 is compatible with these results and remains unproved by this review. The three-row argument does not control supports of sizes 4 through 8. In particular, checking only the antipodal rows for a larger proposed support would give necessary conditions; any surviving solution would still need the full inverse to be ternary at all 512 vertices before it could serve as a counterexample.

This review used the checked round-237 inverse and two-erasure sources and the parent's saved exact 3375-case preliminary calculation. No compiler, solver, or large enumeration was run by the reviewer. No novelty claim is made.
