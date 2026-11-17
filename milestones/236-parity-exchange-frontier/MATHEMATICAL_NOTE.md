# Round 236: larger parity exchanges and neighbour-count reconstruction

The construction hypothesis was that three replacements in a saved 96-vertex parity set might permit a 192-edge snake when the opposite parity set and the path order are free. Audited native degree models exclude all 145 such families. A bounded four-replacement search leaves three queried families unresolved. This round also proves necessary conditions that explain how additions and deletions must interact, with no new snake or global bound.

## Retained vertices require balanced changes

Let \(P\) and \(Q\) be the vertex sets of two induced paths of positive length. Write \(A=Q\setminus P\) for additions and \(D=P\setminus Q\) for deletions. At a retained vertex \(v\), let \(e_P(v),e_Q(v)\) be the endpoint indicators. Splitting each selected neighbour set into retained and changed neighbours gives

\[
|N(v)\cap A|+e_Q(v)=|N(v)\cap D|+e_P(v).
\]

Indeed, the retained neighbours contribute equally to the two degrees, while the degrees are \(2-e_P(v)\) and \(2-e_Q(v)\). Therefore an internal vertex that remains internal has equally many added and removed neighbours. An old endpoint that becomes internal requires one more added neighbour than removed neighbours.

For a 191-edge seed and a proposed 192-edge snake, every retained vertex of the candidate's 96-vertex parity class is internal in the candidate. Once additions and deletions on the other parity side are proposed, every old internal vertex with unequal added and removed neighbour counts must be deleted. With \(r\) minority replacements there can be at most \(r\) such vertices. The old minority endpoint has a different condition: if retained, it requires one extra added neighbour.

If an added majority vertex touches a minority vertex that is retained and internal in both paths, some deleted majority vertex must also touch that retained vertex. The added and deleted vertices are then at Hamming distance two. The incidence hypothesis matters: the path \(0,1,3,7\) in \(Q_3\) extends to \(0,1,3,7,6\) without any deletion, because the addition touches an old endpoint. This directly refutes an unconditional distance-two requirement on every insertion.

The retained-vertex equations are already consequences of the complete degree model. Their proposed use is to select compatible changes or reject a partial proposal early. No speed improvement is established.

## The full neighbour counts determine a vertex set in nine dimensions

Let \(z\) be any integer-valued function on \(Q_9\), and put
\[
b(v)=\sum_{u\sim v}z(u).
\]
Define distance weights
\[
(c_0,c_1,\ldots,c_9)=(0,35,0,-10,0,8,0,-16,0,128).
\]
Then, for every vertex \(a\),
\[
315z(a)=\sum_{v\in Q_9}c_{\operatorname{dist}(a,v)}b(v).
\]

To prove this, substitute the definition of \(b\) and collect the coefficient of each \(z(u)\). If \(k=\operatorname{dist}(a,u)\), exactly \(k\) neighbours of \(u\) have distance \(k-1\) from \(a\), and exactly \(9-k\) have distance \(k+1\); an empty group contributes zero. For odd \(k\), every neighbour has even distance, whose weight is zero. For even \(k\), the five coefficients are
\[
9(35)=315,\quad 2(35)+7(-10)=0,\quad
4(-10)+5(8)=0,\quad 6(8)+3(-16)=0,\quad 8(-16)+128=0.
\]
Thus only \(u=a\) survives. This is an explicit inverse of the cube adjacency matrix, derived by elementary distance counting. No novelty claim is made.

Taking \(z\) to be the difference of two vertex-set indicators shows that identical complete neighbour counts force identical vertex sets. Taking \(z\) to describe changes only on the majority side gives an exact reconstruction of those changes from their effects on all 256 minority vertices. The weighted sum at each majority vertex must belong to \(\{-315,0,315\}\), and its sign must agree with whether that vertex was previously selected.

The word complete is essential. Counts at retained minority vertices are fixed by the endpoint identity, while counts at deleted and previously unselected minority vertices are generally unknown. Setting those unknown counts to zero would discard valid constructions. Since the majority side grows from 96 to 97 vertices, double counting its nine cube incidences gives
\[
\sum_{v\text{ in the minority parity side}} b(v)=9.
\]
The retained minority vertices contribute one if the old minority endpoint is retained, and zero otherwise. The remaining vertices must therefore contribute eight or nine respectively. These are additional ways to express consistency of a complete proposed change, not new independent restrictions on the exact degree model.

An exact integer calculation checks all 262,144 entries of the matrix identity on the labelled cube. The diagonal entries are 315 and all other entries are zero. Four retained-vertex statements and two inverse-support statements passed Lean. The latter prove the five integer recurrences and a finite-list reconstruction theorem under an explicit left-inverse coefficient hypothesis. The cube distance multiplicities and complete labelled-cube instantiation remain the written geometric argument and separate exact calculation. No native infeasibility certificate is checked by these Lean statements.

## Computational results and frontier

All 145 saved sets are natively infeasible with exactly three replacements, retaining 93 of the old 96 vertices. Every model has 768 Boolean variables and 772 constraints, including 512 degree equations enforced only when the vertex is selected. No cycle cut was needed. The independent audit reconstructs every constraint and checks the explicit exchange count, execution arguments, input pins and complete coverage. The models implicitly cover \(145\binom{96}{3}\binom{160}{3}=13\,879\,134\,592\,000\) exchange descriptions before duplicates; these descriptions were not individually enumerated.

Together with the covers for zero, one and two replacements, the candidate's minority class can intersect each saved corresponding class in at most 92 vertices. The earlier majority-side result bounds the other intersection by 95. Thus total overlap is at most 187. Relative to each saved 192-vertex seed, a 193-vertex candidate must omit at least five old vertices and introduce at least six new ones. The argument transports to cube-isometric copies. It relies on the native finite premises and gives no global upper bound. The restricted family with one complete 96-vertex parity class within three replacements of a saved class has exact maximum 191, attained by a seed in the zero-replacement part.

With exactly four replacements, class 139 was natively infeasible after approximately 8.45 seconds. Classes 7, 6 and 0 each returned UNKNOWN after 40 seconds. All four exported models passed the independent audit. There were no feasible selections or cycle cuts. The other 141 classes were not queried at four replacements. Neither UNKNOWN nor an unqueried class is an exclusion.

The next construction work should allow at least four replacements. The three unresolved four-replacement cases remain available, with their frozen model bytes and statuses. A complementary proposed route is to choose additions and deletions jointly using the retained-neighbour balance conditions, then check all still-unknown neighbour counts against the inverse identity before seeking a connected path. This alternative generator is not implemented, and no performance claim is made.

The maintained interval is \(191\le a(9)\le233\), with an independent full rebuild of the contributor's 233 theorem pending. The contributor revision remains 61e6655e7a8aa16ed6f4f56399c381d753a46f5d. The conjecture 196 remains unresolved. Publish this round, preserve all terminal evidence, and pause as requested. Full-source manuscript review last occurred at round 230 and remains due at round 240.
