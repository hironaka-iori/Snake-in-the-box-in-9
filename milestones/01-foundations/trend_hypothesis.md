# A sequence-based hypothesis for the ninth dimension

**Provisional hypothesis: the maximum snake length in dimension nine is 196 edges, or 197 vertices.** This hypothesis is derived from the first eight exact values. It is not established by a construction or an upper-bound proof.

The exact values in [OEIS A099155](https://oeis.org/A099155) are

\[
a(1),\ldots,a(8)=1,2,4,7,13,26,50,98.
\]

## Derivation of the pattern

In the first three-term block, dimensions 3, 4 and 5, the differences determine the same exponential coefficient:

\[
\frac{7-4}{2^4-2^3}=\frac{13-7}{2^5-2^4}=\frac38.
\]

The next block, dimensions 6, 7 and 8, gives the same coefficient:

\[
\frac{50-26}{2^7-2^6}=\frac{98-50}{2^8-2^7}=\frac38.
\]

Subtracting the resulting baseline produces a simple correction:

| Dimension | Exact maximum | Baseline \(3\cdot2^{n-3}\) | Correction |
|---:|---:|---:|---:|
| 3 | 4 | 3 | 1 |
| 4 | 7 | 6 | 1 |
| 5 | 13 | 12 | 1 |
| 6 | 26 | 24 | 2 |
| 7 | 50 | 48 | 2 |
| 8 | 98 | 96 | 2 |
| 9 | **196, predicted** | 192 | **4, hypothesized** |

The proposed continuation keeps the correction constant within each three-dimension block and doubles it between successive blocks:

\[
1,1,1,\quad2,2,2,\quad4,4,4,\ldots.
\]

This gives the extrapolation model

\[
\widehat a(n)=3\cdot2^{n-3}+2^{\lfloor(n-3)/3\rfloor},\qquad n\geq3.
\]

Consequently,

\[
\widehat a(9)=3\cdot64+4=196.
\]

For dimensions 1 and 2 the model is separately assigned the known values 1 and 2. The closed expression is proposed only for dimensions at least 3.

The same model satisfies the three-dimension recurrence

\[
\widehat a(n+3)+6\cdot2^{\lfloor(n-3)/3\rfloor}=8\widehat a(n),\qquad n\geq3.
\]

At the ninth dimension this reads

\[
\widehat a(9)=8a(6)-12=8\cdot26-12=196.
\]

## Why this remains a weak conjecture

Only two complete correction blocks are observed. The rule for subsequent blocks is therefore uncertain. For example,

\[
\widetilde a(n)=3\cdot2^{n-3}+1+\left\lfloor\frac{n-3}{3}\right\rfloor
\]

also agrees with every supplied exact value from dimensions 3 through 8, but predicts 195 at dimension 9. Assigning the first two terms separately makes both models agree with the entire supplied sequence.

The two formulas therefore demonstrate that these data do not determine the ninth value. The geometric correction is selected as a concrete hypothesis because its powers of two are consistent with a possible repeated cube construction. No such construction has been established here. The two descriptions of the 196 model, a baseline correction and a recurrence, express the same numerical evidence.

## Lean verification and the geometric proof obligation

`TrendHypothesis.lean` proves that both models reproduce the supplied exact values, that their ninth predictions are 196 and 195 respectively, and that the geometric model satisfies its general recurrence. The numerical checks use Lean kernel computation. These theorems concern the models; they do not identify either model with the true maximum.

`OptimalityTarget.lean` states the actual 196-edge hypothesis for the cube graph and proves that it is equivalent to both of the following:

1. A valid 196-edge snake exists in the nine-dimensional cube.
2. No valid 197-edge snake exists in that cube.

The second condition rules out every longer path by taking an initial segment. Lean also proves that a 196-edge construction would contain a 192-edge snake. Therefore the existing search for 192 edges remains a necessary first counterexample test against the 191-edge optimum conjecture.

The existing Lean-verified construction has 191 edges. No 196-edge construction or 196-edge upper bound has been obtained. The proposed value 196 is a new sequence-based search target, with low confidence, and the optimality goal remains active.

The subsequent [layer investigation](../02-layer-constructions/layer_investigation.md) checks a concrete construction route. Lean verifies the exact joining condition and a published 98-edge eight-dimensional seed. Restricted computational searches exclude a compatible 97-edge partner for that seed. This supplies an obstruction to that construction, without resolving the global conjecture.
