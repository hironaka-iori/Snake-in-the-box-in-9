# Round 241. The exact distance between neighbour-count profiles in the nine-cube

For two different binary selections in \(Q_9\), the minimum number of labelled neighbour counts that differ is **eight**. Thus any 505 of 512 counts determine the selection, and some 504 fail. For a selection confined to a specified parity side, the corresponding sharp guarantee is 249 of the 256 opposite-side counts. The lower bound below is a written proof. The two selections attaining it are given explicitly in [witness.json](witness.json).

## Why seven changes are impossible

Let \(A\) sum over the nine neighbours, let \(f\) be the difference of two indicators, and write \(w=Af\). Neighbour sums of the two parity restrictions of \(f\) have disjoint supports. It suffices to prove the lower bound for a nonzero \(f\) on one parity side. Its profile \(w\) is on the opposite side. The vertex signs are \(x_j=(-1)^{p_j}\) for the bits of \(p\). For \(I\subseteq\{1,\ldots,9\}\), the character \(\chi_I(x)=\prod_{i\in I}x_i\) has adjacency eigenvalue \(9-2|I|\), by summing its values after each of the nine coordinate flips. Self-adjointness gives the integer identity

\[
\sum_p w(p)\chi_I(p)=(9-2|I|)\sum_p f(p)\chi_I(p).
\]

In particular \(w\ne0\), since the characters form a basis over the rationals and all eigenvalues are odd. Suppose its support \(P\) has at most seven points. Put \(v(p)=(x_1,\ldots,x_9)^{\mathsf T}\). Over the field of five elements the weight-two identity gives

\[
\sum_{p\in P} w(p)v(p)v(p)^{\mathsf T}=\Big(\sum_{p\in P} w(p)\Big)I_9 .
\]

Indeed every off-diagonal entry vanishes and the diagonal entries are identical. The left side has rank at most \(|P|\). For **any** support of size less than nine this forces \(\sum w=0\pmod 5\).

Use the eight signs \(z_j=x_jx_9\) for \(1\le j\le8\). These distinguish the vertices on either parity side. Two sign vectors with identical \(z\) are equal or antipodal, and an antipode changes parity in nine dimensions. The zeroth, first and second squarefree moments of the weights \(w(p)\) at these \(z\)'s vanish modulo five. They are respectively the diagonal sum value \(\sum w\), moments of \(x_jx_9\), and moments of \(x_jx_k\) for \(j\ne k\).

**Moment lemma.** Over a field of odd characteristic, a nonzero weighting of a sign cube that annihilates all squarefree monomials of degrees zero through \(d\) has support of size at least \(2^{d+1}\). For \(d=0\), one nonzero weight cannot sum to zero. For \(d>0\) choose a coordinate on which two support points differ. Both slices are nonzero. Multiplying a monomial in the remaining coordinates of degree at most \(d-1\) by either slice indicator \((1\pm z_j)/2\) shows that both slices satisfy the hypothesis for \(d-1\). Induction gives the bound. This argument applies in particular to the two fields used below. The corresponding minimum-distance theorem for Cartesian evaluation codes is given by López, Rentería-Márquez and Villarreal, Theorem 3.8. [Primary source](https://arxiv.org/pdf/1202.0085#page=10)

Apply the lemma with \(d=2\) over the field of five elements. Fewer than eight positions force every \(w(p)\) to be divisible by five. Actual counts satisfy \(|w(p)|\le9\), so \(w=5u\) with \(u(p)\in\{-1,1\}\) on \(P\). The weight-zero character gives \(9\mid\sum u\). As \(|P|\le7\), the sum is zero. Hence \(|P|\) is even and at most six. The weight-one sums \(\sum u x_j\) are divisible by seven, so their absolute bound of six makes all of them zero. The weight-three sums \(\sum u x_jx_kx_l\) are divisible by three for distinct indices.

Now weight the same \(z\)'s by \(u(p)x_9\) over the field of three elements. Their moments of degrees 0 and 1 are weight-one sums in the original signs. Those of degrees 2 and 3 are weight-three sums, since \(x_9^2=1\). All vanish. The moment lemma now requires at least 16 nonzero positions, a contradiction. This proves the lower bound, including configurations with disconnected distance-eight components.

There is also an independent way to finish once \(5\mid w\). Modulo five, \(Af=0\), so the only Fourier levels of \(f\) are 2 and 7. Character orthogonality holds since 512 is invertible modulo five. The function \(f(x)+f(\bar x)\) keeps only level 2. Its two summands have disjoint support because \(f\) lies on one parity side. This gives a nonzero quadratic on the nine signs with support \(2|\operatorname{supp}f|\). A nonzero multilinear polynomial of degree \(e\) on the sign cube is nonzero at least \(2^{9-e}\) times. Fix all variables outside a highest-degree monomial. Its coefficient remains nonzero under every fixing, so each remaining subcube has a nonzero value. Hence \(|\operatorname{supp}f|\ge64\). On the other hand \(A^2=I\) modulo two, since the nine double flips return to the start and each distinct pair of flips occurs twice. Thus \(f=Aw\pmod2\). Ternarity makes \(f\) zero outside the union of the neighbourhoods of \(P\), giving \(|\operatorname{supp}f|\le9|P|\le63\).

## Two selections attaining eight

Write \(g_r=\mathbf1_{\{0^r\}}-\mathbf1_{\{1^r\}}\), and let \(A_r\) denote adjacency on \(Q_r\). Then \(A_2g_2=0\). The function \(A_4g_4\) is \(+1\) at weight one and \(-1\) at weight three. Its second neighbour sum is \(A_4^2g_4=4g_4\), since the two positive and two negative contributions at every weight-two vertex cancel.

Write vertices as \((y,b,c,t)\) in blocks of lengths \(4,2,2,1\), starting at the least significant bit. Define

\[
f(y,b,c,0)=(A_4g_4)(y)g_2(b)g_2(c),\qquad
f(y,b,c,1)=-g_4(y)g_2(b)g_2(c).
\]

The two selections are the positive and negative supports of \(f\). Each has twenty vertices, all of odd parity. The two-coordinate blocks contribute zero to \(Af\). On the top-bit-zero slice the other blocks give \((A_4^2g_4-g_4)g_2(b)g_2(c)\). On the top-bit-one slice they cancel. Thus \(Af=3g_4g_2g_2\) on \(t=0\) and zero on \(t=1\). Its eight positions and signs are

| Difference | Vertex numbers |
|---|---|
| \(+3\) | \(0,63,207,240\) |
| \(-3\) | \(15,48,192,255\) |

These eight vertices have just four disjoint distance-eight edges among them. The bit differences with weight eight must flip all three of the first blocks. Each vertex therefore has one partner. The four components coexist in an actual profile. This differs from Round 240's generator three-cube, whose antipodal equations admitted an amplitude of 21. All eight amplitudes here have absolute value three. The signed two-coordinate factor and the product adjacency rule occur in Valyuzhenich and Vorob’ev, Section 3. [Primary source](https://arxiv.org/pdf/1807.09139#page=3)

## Consequence for the construction search

Consider the parity side gaining one vertex in a comparison with a 191-edge seed. On this side \(\sum f=1\), hence \(\sum w=9\). The rank identity forces at least nine opposite-side count changes. Equality is rigid. Make the nine sign vectors the columns of a square matrix \(X\) and write \(D=\operatorname{diag}(w(p))\). Over the field of five elements \(XDX^{\mathsf T}=9I\). Both factors are invertible, and \(X^{\mathsf T}X=9D^{-1}\). The dot product between distinct columns is therefore zero modulo five. It equals \(9-2d\), where \(d\) is an even Hamming distance between distinct positions, so \(d=2\).

Translate one position to zero. The other eight become distinct two-element sets, pairwise intersecting. Such a family has a common coordinate. Indeed, starting with two sets \(\{a,b\},\{a,c\}\), a set avoiding \(a\) must be \(\{b,c\}\), after which a fourth distinct set cannot meet all three. Thus the nine positions form the full neighbourhood of one vertex \(q\).

For each \(p\in P\), its antipode has distances seven or nine from every member of \(P\). Since \(f=Aw\pmod2\) and \(f\) is ternary, \(f(\bar p)=0\). The previously proved inverse evaluated at that antipode gives
\[
0=315 f(\bar p)=128 w(p)-16\!\sum_{s\ne p}w(s)=144w(p)-144.
\]
Thus \(w\) is one on \(N(q)\) and zero elsewhere. Invertibility gives \(f=\mathbf1_{\{q\}}\).

A 192-edge snake has 97 vertices of one parity and 96 of the other. For each of the 131 saved seeds, the recorded finite majority-class exclusion rules out retaining the entire old 96-vertex class and adding one vertex. Its gaining side must therefore change at least ten opposite-side counts. The complementary fixed-minority exclusion forces the other side to change as well, contributing at least eight further counts. Their supports are disjoint. **At least 18 labelled neighbour counts must differ from each saved seed.** This inherits the native finite premises of Rounds 231–232. Attainability at 18 and existence of a 192-edge snake are open.
