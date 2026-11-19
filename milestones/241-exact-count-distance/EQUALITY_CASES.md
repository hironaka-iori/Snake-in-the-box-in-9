# All changes attaining eight counts

Up to a cube isometry and reversal of the two selections, the **difference of their indicators** attaining eight count changes is the displayed 40-vertex signed function. The two selections may also contain identical arbitrary vertices off its support. The geometric reduction is written. The final six configurations use exact native inverse evaluations.

## Four blocks of coordinates

Use the signs, moments and notation of the [lower-bound proof](MATHEMATICAL_NOTE.md). A profile supported at eight points lies on one parity side, since two nonzero parity restrictions would have disjoint profiles with at least eight points apiece. If all eight nonzero weights were divisible by five, write \(w=5u\) with \(u=\pm1\). Each weight-one sum \(\sum ux_j\) is divisible by seven, is even, and has absolute value at most eight. It must be zero. The weight-three argument modulo three from the lower bound would require at least sixteen positions. Thus some weight survives modulo five. The degree-two moment lemma then forces all eight weights to survive.

Let \(X\) be the \(9\times8\) sign matrix and \(D\) the diagonal matrix of those weights over \(\mathbb F_5\). From \(XDX^{\mathsf T}=0\), its row space is orthogonal to itself under the nondegenerate bilinear form with matrix \(D\). Its dimension \(r\) is at most four. Choose \(r\) independent physical coordinate rows. Their columns are distinct up to sign, since equality up to sign on the basis rows would imply equality up to sign on all nine, contradicting distinctness on one parity side. At most \(2^{r-1}\) signs up to global sign exist. Therefore \(r=4\), and all eight projective sign patterns occur.

Every physical coordinate row is a linear form \(L\) in these four independent signs over \(\mathbb F_5\). It takes values \(\pm1\) on the eight representatives and hence also on their negatives. On the full four-sign cube \(L^2=1\). For two distinct coordinates \(i,j\) the coefficient of their product in \(L^2\) is \(2a_i a_j\), where the \(a_i\) are the coefficients of \(L\). Independence of the sign characters over \(\mathbb F_5\) forces these products to vanish. Thus each row is one of the four basis rows up to sign.

Translate a support vertex to zero. The sign at each physical coordinate is now positive at that vertex, so within each of four nonempty blocks all signs agree. The even representatives of the 16 constant-on-block words are exactly the eight support vertices. Complementation interchanges parities since the total length is odd. Permuting blocks and their coordinates leaves the six unordered partitions in the table below. No distance-eight connectivity assumption enters this classification.

## Which block geometries survive

For one partition let \(P\) be its eight even vertices. They form a subgroup under bitwise addition. Index them by three bits by setting the last block to zero and complementing all nine bits when needed to reach even parity. This is a linear parametrization, since both the block word and its parity depend linearly on the index. Let \(N(P)\) be the union of their ordinary distance-one neighbourhoods. The identity \(f=Aw\bmod2\) and ternarity imply \(f=0\) outside \(N(P)\).

Extend each character \(\chi_j(i)=(-1)^{\operatorname{popcount}(i\mathbin{\&}j)}\) by zero off \(P\), for indices \(i,j=0,\ldots,7\). Translation by \(P\) preserves \(N(P)\) and commutes with \(A^{-1}\). Consequently, if a profile \(w\) on \(P\) has inverse zero outside \(N(P)\), each of its character components has that property individually. Indeed, the character projection is the signed average of the eight translations, and every translated inverse is zero there.

The table gives the largest absolute entry of \(315A^{-1}\chi_j\) on the complement of \(N(P)\), in character order. Each entry is the maximum of integer sums of eight terms. For a point \(x\) each term is \(\chi_j(i)\rho(d(x,p_i))\), using \(\rho(1),\rho(3),\rho(5),\rho(7),\rho(9)=35,-10,8,-16,128\) and zero at even distances. The [calculation](classify_supports.py) and its [configuration-by-configuration receipt](four-block-certificate.json) give the actual vertices in this indexing.

| Block lengths | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 6, 1, 1, 1 | 28 | 42 | 36 | 42 | 36 | 42 | 36 | 30 |
| 5, 2, 1, 1 | 56 | 48 | 42 | 42 | 36 | 48 | 42 | 30 |
| 4, 3, 1, 1 | 56 | 42 | 48 | 42 | 36 | 42 | 48 | 30 |
| 4, 2, 2, 1 | 104 | 72 | 72 | 84 | 72 | 84 | 84 | 0 |
| 3, 3, 2, 1 | 56 | 48 | 48 | 48 | 42 | 42 | 42 | 30 |
| 3, 2, 2, 2 | 94 | 114 | 126 | 114 | 126 | 114 | 126 | 210 |

Only the last character for block lengths \(4,2,2,1\) can have a nonzero coefficient. For that character the exhibited profile is \(3\chi_7\). Invertibility makes the inverse of any scalar multiple proportional to the exhibited ternary function. Its value \(+1\) at vertex 1 fixes the absolute proportionality factor to one for any nonzero ternary inverse. The two orientations are therefore the only ones in these coordinates.

In particular an eight-count change replaces exactly twenty memberships by twenty others on the affected parity class. On resumption the finite construction question is whether any isometric copy has its negative support inside a saved seed and its positive support outside. Such a sign match would still require a compatible change on the opposite parity class and verification of a connected induced path.

## A written check of which table entries vanish

Identify each parity side with \(G=\mathbb F_2^9/\langle(1,\ldots,1)\rangle\) by taking its unique representative of that parity. Adjacency between the sides is the sum \(C\) of the nine coordinate shifts. Let \(b_j\) denote a full block flip and \(m_j\) its block length. In the quotient the four \(b_j\) generate \(P\) and their only relation is that their sum vanishes. A character \(\chi\) of \(P\) has block signs \(\sigma_j=\chi(b_j)\) of product one.

The characters of \(G\) extending \(\chi\) select subsets with \(k_j\) coordinates in block \(j\), where \((-1)^{k_j}=\sigma_j\). The total is even, as required on the quotient. Put \(l_j=m_j-2k_j\). The adjacency eigenvalue is \(\sum_j l_j\), always odd. The Fourier transform of \(\chi\mathbf1_P\) on each such extension is eight.

Suppose its inverse is zero off \(N(P)\). This inverse transforms by \(\chi\) under translations by \(P\), so on every occupied coset \(e_i+P\) it is a multiple of a translate of \(\chi\mathbf1_P\). On extending characters its Fourier transform is therefore eight times a linear combination of the nine coordinate signs. It also equals eight divided by the adjacency eigenvalue. Permuting coordinates within each block preserves the allowed extensions and the eigenvalue. Averaging the linear representation over these permutations gives constants \(c_j\) such that
\[
\frac{1}{\sum_j l_j}=\sum_j c_j l_j
\]
for every admissible choice of block counts.

Possible values of each \(l_j\) are spaced by four. If one block has three possible values, the second difference of the left side is nonzero, whereas a linear function has zero second difference. The same contradiction follows from a mixed difference if two blocks each have at least two values. The three denominators in either difference are \(a,a-4,a-8\) with odd \(a\), and the second difference of their reciprocals is \(32/[a(a-4)(a-8)]\).

Blocks of size five or six always give three values. The partitions containing both a four and a three, or two threes, always have two varying blocks. For \(4,2,2,1\), an even \(k_j\) on the four-block gives three values, and an even \(k_j\) on a two-block gives a second varying block. All three must be odd, and the singleton must then also be odd. This is character seven in the table. For \(3,2,2,2\) each two-block must have odd \(k_j\), else there is a second varying block. The three two-blocks then have \(l_j=0\), and the three-block has \(l=1,-3\). No constant \(c\) satisfies \(1/l=cl\) at both values. The displayed witness proves that the remaining character has zero exterior.
