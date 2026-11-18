# Round 239: recovery after four missing counts

The written argument below excludes a nonzero ternary function f on Q9 whose neighbour sums Af are supported on at most four positions. Thus any 508 of 512 neighbour counts determine a binary selection uniquely. The proof uses the checked round-238 three-erasure result and a written classification of distance-eight pairs. The native finite audit is now complete: 11440 column compositions give 1149 valid ordered descriptions, 105 cube-set orbits and 87 metric classes; all 7047 ternary right-hand-side cases have no nonzero integer solution. A separate direct enumeration of 2731135 triples recovers the same 87 classes. New Lean modules check the 87 literal matrix implications; their complete accepted status must be read from the final replay receipt. Geometric coverage and the mixed-parity-to-cube assembly retain written/native scope. No novelty claim is made.

## Reduction to four positions of one parity

Split f into its restrictions to the two cube parity sides. Adjacency sends each restriction to the opposite side. If four missing positions have mixed parity, each restricted neighbour-sum profile is supported on at most three positions. The three-erasure theorem makes both restrictions zero. Only four positions of one parity remain.

Let these positions be p_0,p_1,p_2,p_3, and let w_i=Af(p_i). Applying the cube inverse at their antipodes gives

\[
Mw=315s,\qquad s_i\in\{-1,0,1\}.
\]

The matrix is symmetric, with diagonal 128. Its off-diagonal coefficient is -16,8,-10,35 at distance 2,4,6,8 respectively. All arguments below apply to arbitrary integer w; the automatic bounds |w_i|<=9 are unnecessary.

The following divisibility observation is used repeatedly. If D x=315N for integers D>0,x,N, then D/gcd(D,315) divides N. If |N| is smaller than that positive divisor, N=x=0.

## Geometry of the coefficient 35

Join two of the four positions when their distance is eight. This is exactly the graph of the odd matrix coefficient 35. Translate one position to zero. Each distance-eight neighbour is J xor e_i, where J is the all-ones word. Two distinct such neighbours have distance two. Thus the graph is triangle-free.

The seven possible unlabelled graph types are: empty; one edge; two disjoint edges; a two-edge path and an isolated vertex; a three-leaf star; a three-edge path; and a four-cycle. With three edges the only other type contains a triangle, and a triangle-free graph on four vertices has at most four edges, with equality only for a four-cycle.

### Empty graph

All matrix coefficients are even, so parity forces s=0. If m=max_i|w_i|, a row attaining m gives 128m<=48m. Therefore w=0.

### One edge

Call its unknowns x,y and the remaining unknowns z,t. The last two RHS values vanish by parity. Put m=max(|x|,|y|), h=max(|z|,|t|). Since every other coefficient has absolute value at most 16, their rows give

\[
112h\le32m,\qquad93m\le315+32h.
\]

Consequently 587m<=2205, so m<=3 and h<=6/7. Integrality gives z=t=0. The remaining coefficient-35 two-by-two system vanishes by the three-erasure arithmetic proof.

### Three-leaf star

Every leaf-pair coefficient is -16. Subtracting two leaf rows gives 144(y-z)=315(t-u), with |t-u|<=2. Since 144 divides neither 315 nor 630, the two unknowns and RHS values agree. All leaf unknowns are therefore equal. The remaining system has matrix

\[
\begin{pmatrix}128&105\\35&96\end{pmatrix}.
\]

Its determinant is 8613 and its gcd with 315 is 9. Hence 957 divides 128t-35s, whose absolute value is at most 163. It must vanish, forcing s=t=0 and all unknowns zero.

### Three-edge path

In path order its matrix is

\[
M=\begin{pmatrix}
128&35&-16&-10\\
35&128&35&-16\\
-16&35&128&35\\
-10&-16&35&128
\end{pmatrix}.
\]

Indeed, successive positions can be written 0, J xor e_i, e_i xor e_j, J xor e_i xor e_j xor e_k. Distinctness and the absence of a closing distance-eight edge force i,j,k distinct. The nonconsecutive distances are 2,2,6.

Adding and subtracting reversed pairs of rows gives the matrices

\[
M_+=\begin{pmatrix}118&19\\19&163\end{pmatrix},
\qquad
M_-=\begin{pmatrix}138&51\\51&93\end{pmatrix}.
\]

Their RHS entries are 315 times integers of absolute value at most 2. Their determinants are 18873 and 10233, each with gcd 9 with 315. The reduced divisors 2097 and 1137 exceed every corresponding adjugate numerator bound, respectively 364 and 378. Thus all sums and differences of unknowns vanish.

### Four-cycle

Opposite vertices have distance two. Subtracting opposite rows, with coefficient 144 as above, forces opposite unknowns and RHS values to agree. The remaining matrix is

\[
\begin{pmatrix}112&70\\70&112\end{pmatrix}.
\]

Adding gives 182(x+y)=315(s+t). Since gcd(182,315)=7 and |s+t|<=2, divisibility forces x+y=s+t=0. The first row then becomes 42x=315s, or 2x=15s. Parity and |s|<=1 force s=x=0.

### Two-edge path and an isolated vertex

Put the centre at zero and its leaves at J xor e_i and J xor e_j. The isolated position q has weight k in {2,4,6}. Its distances to the leaves are 10-k when the corresponding coordinate belongs to q and 8-k otherwise. Excluding further distance-eight edges gives exactly the following coupling triples (alpha,beta,gamma), up to swapping the leaves:

\[
(-16,-10,-10),\ (8,8,8),\ (8,-10,8),\ (8,-10,-10),
\ (-10,-16,-16),\ (-10,8,-16),\ (-10,8,8).
\]

The centre-and-leaves block is

\[
K=\begin{pmatrix}128&35&35\\35&128&-16\\35&-16&128\end{pmatrix},
\quad \det K=1711584,
\quad \operatorname{adj}K=
\begin{pmatrix}16128&-5040&-5040\\-5040&15159&3273\\-5040&3273&15159\end{pmatrix}.
\]

Let v=(alpha,beta,gamma)^T and L=(adj K)v. The isolated RHS is zero by parity. If h is its unknown, block elimination gives

\[
D h=-315L^{\mathsf T}(s,t,u),\qquad
D=128\det K-v^{\mathsf T}L.
\]

The seven small exact calculations are:

| (alpha,beta,gamma) | D | gcd(D,315) | sum of absolute entries of L |
|---|---:|---:|---:|
| (-16,-10,-10) | 214493184 | 9 | 364608 |
| (8,8,8) | 216981504 | 9 | 262656 |
| (8,-10,8) | 215926884 | 9 | 353052 |
| (8,-10,-10) | 212751360 | 45 | 679104 |
| (-10,-16,-16) | 211258368 | 9 | 489024 |
| (-10,8,-16) | 214263360 | 45 | 406224 |
| (-10,8,8) | 213497856 | 9 | 637632 |

In every row, D/gcd(D,315) exceeds the last column. Therefore the scalar product vanishes and h=0. The remaining three unknowns vanish by the three-erasure arithmetic theorem.

### Two disjoint edges

Normalize the first edge as 0,J xor e_i and the second as q,q xor J xor e_j. Put k=weight(q), a=1 if i belongs to q, and b=1 if j belongs to q. The four cross distances are

\[
\begin{pmatrix}
k&8-k+2b\\
8-k+2a&k+2-2(a+b)
\end{pmatrix}
\]

when i and j are distinct; when i=j, the bottom-right entry is k and a=b. All four cross distances must belong to {2,4,6}. Taking k=2,4,6 and swapping the two edges or their endpoints leaves exactly five symmetric cross-coefficient matrices:

\[
C_1=\begin{pmatrix}-16&-10\\-10&-16\end{pmatrix},\quad
C_2=\begin{pmatrix}8&8\\8&8\end{pmatrix},\quad
C_3=\begin{pmatrix}8&-10\\-10&8\end{pmatrix},
\]
\[
C_4=\begin{pmatrix}-16&-10\\-10&8\end{pmatrix},\quad
C_5=\begin{pmatrix}8&8\\8&-10\end{pmatrix}.
\]

For example, the apparently asymmetric block [[-10,-16],[8,-10]] becomes C_4 after swapping the second edge's endpoints. The same-coordinate cases give C_1,C_2,C_3. The distinct-coordinate cases give C_4,C_5 and their endpoint swaps.

Let B=[[128,35],[35,128]]. The full matrix is [[B,C],[C,B]]. Adding the two block equations gives

\[
(B+C)X=315S,\qquad |S_i|\le2,
\]

where X is the vector of sums of corresponding unknowns. The following table lists the reduced determinant and the largest adjugate numerator bound:

| C | det(B+C)/gcd(det(B+C),315) | bound for RHS entries of absolute value at most 2 |
|---|---:|---:|
| C_1 | 3973 | 274 |
| C_2 | 5549 | 358 |
| C_3 | 851 | 322 |
| C_4 | 1623 | 322 |
| C_5 | 4733 | 358 |

All sums vanish, so both the unknowns and the original RHS values in the second block are the negatives of those in the first. The first block then gives (B-C)(x,y)^T=315(s,t)^T with s,t ternary. Its bounds are:

| C | det(B-C)/gcd(det(B-C),315) | bound for ternary RHS |
|---|---:|---:|
| C_1 | 297 | 189 |
| C_2 | 217 | 147 |
| C_3 | 275 | 165 |
| C_4 | 339 | 189 |
| C_5 | 1759 | 165 |

Divisibility again forces zero. This closes the seventh graph type and the written four-erasure proof.

## Complete finite coverage

Translate the first missing position to zero, leaving three distinct nonzero even-weight nine-bit words. A coordinate is described by its column pattern in {0,1}^3. Let n_r count the coordinates of pattern r, ordered 000,001,010,011,100,101,110,111. These eight nonnegative counts sum to 9. There are binomial(16,7)=11440 count vectors before restrictions.

1. Enumerate every weak composition of 9 into eight ordered parts. Construct its three canonical nine-bit words by listing columns in increasing pattern order. Require four distinct words including zero, all of even weight. Equivalently all six pairwise distances belong to {2,4,6,8}.
2. Optionally identify unordered quadruples under 24 relabellings. For a permutation sigma of the four points, put b_0=0 and let b_1,b_2,b_3 be a column's bits. Relabelling and translating the new first point to zero sends that column to (b_sigma(1) xor b_sigma(0), b_sigma(2) xor b_sigma(0), b_sigma(3) xor b_sigma(0)). This permutes the eight patterns. Keep the lexicographically least count vector among the 24 images.
3. Form its antipodal four-by-four matrix and solve all 81 ternary RHS vectors by exact integer adjugates. Strict diagonal dominance, 128>3*35, gives a positive determinant. Keep only integral solutions with all |w_i|<=9. For exact support four, every w_i must be nonzero. The global sign symmetry permits 40 nonzero RHS representatives; taking all 81 avoids that extra coverage obligation.
4. For any arithmetic survivor, reconstruct the full inverse and check it directly as below.

The six distances are

\[
\begin{aligned}
d(0,a)&=n_{100}+n_{101}+n_{110}+n_{111},\\
d(0,b)&=n_{010}+n_{011}+n_{110}+n_{111},\\
d(0,c)&=n_{001}+n_{011}+n_{101}+n_{111},\\
d(a,b)&=n_{100}+n_{101}+n_{010}+n_{011},\\
d(a,c)&=n_{100}+n_{110}+n_{001}+n_{011},\\
d(b,c)&=n_{010}+n_{110}+n_{001}+n_{101}.
\end{aligned}
\]

Any normalized ordered quadruple is carried to its canonical column realization by a coordinate permutation. Thus this is a complete reduction under cube isometries. Different column-count orbits can nevertheless have the same distance matrix. Matrices may be deduplicated to reuse arithmetic solutions; every surviving solution would still require reconstruction for each relevant column-count orbit. An eliminated matrix eliminates every orbit producing it.

## Full inverse validation and interpretation

For any apparent survivor at p_0,...,p_3, compute at all 512 vertices

\[
N(v)=\sum_{i=0}^3 k(d(v,p_i))w_i,
\]

where k is 35,-10,8,-16,128 at distances 1,3,5,7,9 and zero at even distances. A ternary inverse requires every N(v) to belong to {-315,0,315}. Put f(v)=N(v)/315 and independently recompute every nine-neighbour sum, checking that Af equals the proposed four-supported profile exactly. Such a survivor would contradict the written classification or arithmetic above and must be investigated before publication.

A verified nonzero f would give two binary selections from its positive and negative supports, with identical counts outside the four positions. This would be a counterexample to binary-selection recovery, with no snake conclusion by itself.

The completed exact audit has no nonzero integer survivor, without imposing a bound on the four unknown count differences. The direct triple enumeration independently confirms the entire metric catalogue. The written theorem gives recovery from any 508/512 counts, or 252/256 opposite-side counts for a selection on a known parity side. The minimum support of a nonzero ternary neighbour-sum profile is between 5 and 9; the upper example is a function supported at one vertex. The proposed minimum 9 remains open.

Lean scope must distinguish the existing inverse and three-erasure theorems, the mixed-parity reduction, geometric classification, and new arithmetic exclusions. A native audit of every count vector does not by itself make the full four-erasure conclusion a Lean theorem. This note supplies a complete written proof and a separate computational falsification plan; new kernel acceptance must be reported from actual receipts.


## Up to eight missing positions without a distance-eight pair

Let E be any set of at most eight cube vertices containing no pair at Hamming distance eight. The neighbour counts outside E uniquely determine a binary selection. This permits mixed parity in E and is a written deduction from the existing cube inverse.

For the ternary difference f of two selections, put w_i=Af(p_i) at the k missing positions. The antipodal matrix has diagonal 128 and off-diagonal entries in {0,-10,8,-16}; distance eight is the only source of the odd coefficient 35. All equations have even left sides and RHS 315s_i with s_i ternary, so s_i=0. With M=max_i|w_i|, a row attaining M gives

\[
128M\le16(k-1)M\le112M.
\]

Thus every missing count difference is zero, and the inverse gives f=0. If no counts are missing, inverse injectivity applies directly.

The conditional threshold eight is sharp. Let E be the nine neighbours of a vertex v. Every pair in E has distance two, and the empty selection and singleton {v} agree in every count outside E. The antipodal nine-by-nine matrix is 144I-16J and annihilates the all-ones vector. This is an explicit binary-selection example; it supplies no longer snake.

For unrestricted missing positions, the current result remains four-erasure recovery. Any counterexample with support size five through eight must have a distance-eight pair in its neighbour-sum support. The proposed unrestricted minimum support nine remains unresolved. The geometric/inverse deduction here is written; any separate Lean scalar-inequality check must retain that narrower scope.

## Current validation records

- data/four-count-audit.json: PASS_NO_NONZERO_INTEGER_SOLUTIONS; 11440 column compositions, 1149 valid ordered descriptions, 105 point-set orbits, 87 metric classes, 7047 ternary RHS cases, no nonzero integer solution. The arithmetic treats unbounded integer unknowns.
- data/independent-geometry.json: PASS_GEOMETRY_COVERAGE; all binomial(255,3)=2731135 triples of distinct nonzero even-weight vertices after fixing the first point at zero; exactly the same 87 canonical metric classes.
- lean/FourMatrix239_000.lean through FourMatrix239_086.lean: literal matrix implications using checked adjugate identities and finite divisibility certificates. Root owns the aggregate replay receipt and must confirm all 87 modules before publishing the complete Lean-checked arithmetic claim.
- paper-addition.tex and short-addition.tex: manuscript passages with a publication-gate comment for that aggregate receipt. Neither passage claims an assembled Lean four-erasure theorem for the cube.

The geometric classification, parity decomposition and actual-cube application are complete written proofs. Their remaining Lean assembly is explicit. Native coverage, kernel-checked matrix arithmetic, and the written cube deduction have distinct scopes. No counterexample or longer snake was found; the global snake-length interval is unchanged. Root will finalize compilation, publication and the pause after round 239.

## Completed kernel stage

All 87 matrix implications passed the guarded Lean runner; see data/matrices-replay.json. The three modules in data/dominance-replay.json also passed, including list-sum bounds and the final even-row conclusion. The initial combined dominance module exceeded the retained memory limit. Its split form required one constant-normalization repair before acceptance. Failed and accepted records are retained separately. These arithmetic checks do not remove the stated geometric assembly gap. Both updated manuscripts compiled successfully.
