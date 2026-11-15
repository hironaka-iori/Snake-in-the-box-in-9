# Checked integer degree and residual-certificate lemmas

`Degree219.lean` passed Lean4.19.0 with a Std-only import and four accepted dependency reports. Compilation began only after the parent reported the first LP batch terminal and explicitly reserved the compiler slot. No solver or software tests were launched for this task.

The prior `31-joint-counter-soundness/lean/WeightedExcess.lean`, `58-share-pressure/lean/WeightedCeiling.lean` and `137-actual-block-assembly/lean/DegreeSum137.lean` were inspected for reuse. Their weighted arguments concern different overlap, scalar-ceiling and degree-count settings and import Mathlib. No directly reusable short residual-certificate lemma was found in those sources. This bounded inspection does not claim that no such result exists elsewhere.

## Accepted exports

`selected_degree_iff` proves, over the integers, that under \(x,e\in\{0,1\}\), \(e\le x\), and \(0\le s\le d\),

\[
(x=1\Longrightarrow s=2-e)
\quad\Longleftrightarrow\quad
2x-e\le s\le d-(d-2)x-e.
\]

For an unselected vertex the inequalities reduce to the available bounds on its neighbour count, so they do not incorrectly forbid selected neighbours of an unselected vertex. The available degree \(d\) may vary by vertex and may be less than two. All subtractions are signed.

`edge_product_iff` proves, for integer Boolean \(x,z\),

\[
y=xz\quad\Longleftrightarrow\quad
0\le y,\quad y\le x,\quad y\le z,\quad y\ge x+z-1.
\]

There is no separate Boolean premise on \(y\); these conditions force the correct integer product.

`residual_term_le` proves \(rv\le\max(r,0)\) for integer \(0\le v\le1\). `residual_certificate_bound` combines nonnegative integer multiples of inequality rows, arbitrary signed integer multiples of equality rows, and these residual allowances. It derives the scaled objective upper bound from the row premises and an explicit exact algebraic expansion equality. A short private list-sum inequality lemma carries out the summation; no new definitions or matrix framework are introduced.

## Exact scope of the certificate statement

For a concrete system \(Av\le b\), \(Ev=f\), scale \(D\), inequality multipliers \(Y\ge0\) and arbitrary equality multipliers \(Z\), the intended residual is

\[
r=Dc-A^{\mathsf T}Y-E^{\mathsf T}Z.
\]

The theorem's algebraic identity premise is the corresponding expansion

\[
D(c\cdot v)=\sum_iY_i(Av)_i+\sum_iZ_i(Ev)_i+\sum_jr_jv_j.
\]

The conclusion is

\[
D(c\cdot v)\le\sum_iY_i b_i+\sum_iZ_i f_i+\sum_j\max(r_j,0).
\]

The source proves multiplication of row inequalities, permits signed equality multipliers, and proves residual compensation. It does not prove the expansion automatically from a matrix data structure. A numerical application must independently verify the actual arrays, scale, multipliers, exact residual coefficients and that identity. The identity is an equality certificate condition; an objective-bound inequality is not assumed. Interpreting the scaled bound as an unscaled upper bound additionally requires \(D>0\).

All variables and coefficients in this source are integers. In particular, its box-variable statement applies to the intended Boolean assignments. It does not state an upper-bound theorem for arbitrary fractional LP solutions. Rational multiplier candidates can be scaled to integers; their origin in a numerical LP gives no certificate until exact verification succeeds. No numerical bound or accepted LP certificate is claimed.

## Verification record

- Source `lean/Degree219.lean`: SHA-256 `a3fc1ff1d763184c1331d0b9841edad92873738d46a0b0753727c4e709400a6e`.
- Object `build/Degree219.olean`: `909cf525957b698c949d93f7c2eceeeb6a2742e194651094b54aa8ff293aa4fc`.
- Receipt `data/Degree219-audit.json`: `13ee4f92af48fcc59cfb04ec28b168ea5f73ac0e623b3979137b69cab4c7e0c1`.
- Log `logs/Degree219-1794707709585083400/compiler.log`: `6c2f37994e0a43677b9524258eadf925c54d3809437738ccd97b33be4411b3da`.

The two encoding equivalences use `propext`, `Classical.choice` and `Quot.sound`. The residual-term and weighted-certificate results use only `propext` and `Quot.sound`. No admitted statement, new axiom or native decision call occurs in the accepted source.

The accepted run took2.086seconds, with one compiler, `-j1 -s8192`, a60-second limit,256MiB private-memory ceiling,768MiB free-memory reserve and1GiB startup gate. Startup free memory was1,661,419,520bytes; minimum sampled free memory was1,439,657,984bytes; maximum sampled compiler private memory was120,426,496bytes. No resource stop occurred. Sampling does not establish an unsampled exact memory maximum.

Three failed elaboration attempts are preserved in `logs/Degree219-1794707671989715900`, `logs/Degree219-1794707688980580200` and `logs/Degree219-1794707699171164900`. They concerned a reserved type-parameter name, exposing a function application before rewriting, and supplying the reflexive inequality after that rewrite. The mathematical premises and conclusions were unchanged. Their partial reports are not accepted proof evidence.

The parent was notified immediately after the accepted compiler run became terminal, and the slot was released. No further compiler was launched.
