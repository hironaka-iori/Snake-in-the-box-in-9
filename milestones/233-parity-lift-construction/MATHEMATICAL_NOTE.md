# Round 233: parity lift and deletion obstruction

The round examines a possible explanation of 26->50 and 50->98 edges. It produces a general construction criterion and a deletion obstruction, with no new Q9 record or global upper bound.

## Construction criterion

Let c(x) be parity in Q_n. For S subset Q_n, select U = {(x,c(x)): x in S} in Q_(n+1). Every opposite-parity vertex is uniquely z_y = (y,1-c(y)). Its neighbours in U correspond exactly to N[y] intersect S: equality gives a vertical edge and base adjacency gives an edge within one face.

Construct a labelled graph on S. Each y for which N[y] intersect S has exactly two vertices joins those vertices. A Hamiltonian path, interleaved with its labels, gives an induced snake of 2|S|-2 edges. Labels cannot repeat, since each has one fixed unordered pair and a simple Hamiltonian path cannot repeat a pair. Conversely, a snake whose majority class is U gives this ordering and these labels.

Every even-parity vertex (x,b) satisfies b=c(x). Thus projection identifies every even-parity selected class with one subset S of Q_n. An odd majority class is handled by flipping the last coordinate. Consequently, for k>=2, a snake of 2k-2 edges exists in Q_(n+1) exactly when some k-set S in Q_n has the stated Hamiltonian contraction. In particular, 192 edges in Q9 are equivalent to a suitable 97-set in Q8. This criterion retains the full existence difficulty.

The finite hypothesis restricts S to a saved induced base path P after r deletions. If P has m edges, the resulting length would be 2m-2r. One omission would give 26->50, 50->98 and 98->194. Zero or two omissions of the 98-edge parent would give 196 or 192. These arithmetic equalities alone provide no construction. The lift is not a cube isometry.

## Complete finite cover

One saved parent in each of dimensions 5, 6, 7 and 8 has respectively 13, 26, 50 and 98 edges. Every deletion set of size zero, one or two was covered: 106, 379, 1327 and 4951 cases, totalling 6763.

There are 6698 isolated-vertex exclusions, 27 excess-leaf exclusions, two disconnected graphs, eight native infeasible circuit queries, and 28 actual witnesses. The witnesses are two 24-edge and 26 22-edge snakes, all in Q6, with all vertex pairs checked. No query remains unresolved. All 6657 cases from the Q6, Q7 and Q8 parents have an isolated vertex, so their exclusions require no solver conclusion. The eight native infeasibility results concern only the Q5 parent. There is no exhaustive claim over all parents of a dimension. Finite extraction and solver results are separate from Lean proofs.

## Deletion obstruction

Suppose x is initially isolated in the contraction on P. If x is retained and every deletion is farther than distance two from x, x remains isolated. Any potentially incident label y belongs to N[x], and every member of N[y] lies within distance two of x. Thus N[y] intersect P is unchanged by those deletions and cannot acquire exactly two selected vertices.

Let I be the initial isolated set. Every x in I must lie within distance two of a deletion, including the case when x itself is deleted. If each parent vertex covers at most K members of I within distance two, any Hamiltonian contraction with at least two vertices requires |I|<=rK. This condition is necessary only.

For the saved Q8 parent, |I|=69 and K=17. Since 4*17=68<69, at least five deletions are required. Its entire deletion-only lift family therefore has length at most 196-10=186, even with arbitrary Hamiltonian order and eligible labels. This excludes the 192, 194 and 196 targets for that parent; it gives no global upper bound for Q9.

For the saved Q7 parent the values 37 and 12 require at least four deletions, giving a restricted ceiling of 92 edges. For the saved Q6 parent, 10 and 6 require at least two deletions. More strongly, the union covered by any two deletions contains at most nine of the ten initial isolated vertices. At least three deletions are therefore required, giving a restricted ceiling of 46 edges. Disjoint repair-neighbourhood triples for the Q7 and Q8 parents also give weaker three-deletion certificates.

## Vertical crossings and verification

A retained label y already sees its own lift. It is eligible exactly when y has one retained base neighbour. Since P is induced, such y are the ends of nonsingleton retained components. At most r+1 components remain after r deletions, hence at most 2(r+1) eligible retained labels. Each used retained label contributes one vertical crossing, while labels outside S contribute none. These lifts therefore have at most 2(r+1) crossings. The component count and whole-path interpretation remain written arguments.

The two new Lean modules establish four lift statements and two local-deletion statements. Accepted compiler receipts determine their checked status. Cube projection, radius-two interpretation, finite extraction, incidence counting and solver conclusions retain their separate written or computational scope. No novelty claim is made.

## Paused frontier

Rounds 231 and 232 exclude retaining any entire saved 96-vertex parity class in a 192-edge snake, under their native finite premises. The next constructive family replaces one vertex of a saved minority class, with its opposite class and order free. This family is unsearched. Only neighbours of removed or inserted vertices change label eligibility. The present round explains why choosing a new class solely by deleting from an old lower-dimensional path is too restrictive for these parents.

The maintained interval is 191<=a(9)<=233; an independent full rebuild of the contributor's 233 theorem remains pending. The conjecture a(9)=196 is unresolved. Pause after publication of this round and resume only on user instruction.
