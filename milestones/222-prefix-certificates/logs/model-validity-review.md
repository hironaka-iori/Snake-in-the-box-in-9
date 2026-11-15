# Independent mathematical challenge of the fixed-parent model

No model-validity obstruction was found. Every actual compatible 93-edge path at either saved root supplies a Boolean assignment satisfying every row of the frozen round-221 long model and the applicable round-222 prefix equalities. Subject to the separate successful audit of complete prefix coverage and all exact leaf certificates, the claimed exclusion therefore implies that arbitrary compatible partners have at most 92 edges and that a one-crossing join with this particular 98-edge parent has at most 191 edges.

This conclusion is conditional on the separate ledger and coefficient audit. This review did not independently replay the tree coverage or its leaf weights. It challenged the geometric interpretation and necessity of the constraints. Only this log was written. No optimizer, compiler, software tests, new search, or edits to existing evidence were performed.

## Source and data inspected

Read the complete current sources `218-direct-partner/scripts/partner_search.py` (142 lines), `219-linear-partner/scripts/linear_partner.py` (120 lines), `219-linear-partner/scripts/cycle_separation.py`, `220-subset-forest/scripts/subset_separation.py` (98 lines), `221-square-parity/scripts/square_separation.py` (103 lines), and the three round-222 producers `prefix_search.py` (78 lines), `prefix_continue.py` (74 lines), and `prefix_deep.py` (82 lines). The 130-line `221-square-parity/scripts/long_separation.py` was read completely in the preceding independent long-model review. Its saved rows were independently reconstructed again in this challenge. Also read the complete `PartnerParity218.lean` and `LayerJoining.lean` sources without compiling them.

Inspected the saved seed, both complete frozen long models, their witness families, and the deep-ledger structure. Read-only integer reconstruction checked every row of both long models against the necessary families described below. No producer module was imported. The saved seed has 99 distinct vertices, endpoints 0 and 78, and exactly the consecutive pairs are cube-adjacent; all 4851 unordered pairs were checked as mathematical input data. The round-218 and round-219 seed files are byte-identical.

The observed deep ledger has 80 nodes: 27 expanded nodes, three inherited excluded leaves, and 50 new bound-excluded leaves. It has an empty queue and reports `QUEUE_FINISHED`. The maximum observed prefix length is six edges; the configured cap is eight. These observations alone are not a proof of exhaustive coverage. The separate auditor must establish the child lists, inherited exclusions, file hashes, appended rows, and exact leaf bounds.

## Allowed graph and layer geometry

Let $P$ be the saved 98-edge path in $Q_8$, and let $t\in\{0,78\}$ be the joining endpoint. The permitted graph is exactly the induced cube graph on

\[
V_t=\{0,\ldots,255\}\setminus\bigl(V(P)\setminus\{t\}\bigr).
\]

The actual frozen models have exactly this vertex set and every cube edge between its vertices: 158 vertices, 337 edges, and 79 vertices of each parity at each root. No neighbours of parent vertices are additionally removed. No endpoint-location, replacement-size, transition-history, symmetry, or prescribed-terminal restriction is present.

This deletion rule is the correct one for a join across two parallel layers of $Q_9$. For projected labels $u,v\in Q_8$, a vertex in the lower layer and a vertex in the upper layer are adjacent exactly when $u=v$. Their distance is $1+\mathrm{d}_{Q_8}(u,v)$. Thus sharing a projected parent vertex other than $t$ creates an unwanted cross-layer edge. Merely being adjacent to a parent vertex in projection creates no cross-layer edge and must remain allowed; the models correctly retain those vertices.

The parent can be oriented to end at either of its two endpoints. The partner is oriented to begin at that endpoint. In the native representation, adding 256 changes only the new ninth coordinate because every projected label is below 256. The projection labels 0 and 78 are cube vertices, not positions in the path. The source distinguishes the root's literal label from its variable index through the `x<label>` lookup. The two orientations cover the two possible endpoints of the fixed parent. Reversing traversal or exchanging the two layers introduces no further case.

For this specific one-crossing arrangement, compatibility is exactly $V(P)\cap V(Q)=\{t\}$. It is necessary for an induced joined path and sufficient when both layer paths are induced and the common projected vertex is the intended endpoint pair. The read `LayerJoining` source expresses this condition explicitly and supplies both the join and necessity directions. Its numerical instantiation is not assembled in Lean by this review.

## Assignment supplied by an actual 93-edge path

For an arbitrary compatible induced path $Q=(q_0,\ldots,q_{93})$ with $q_0=t$, assign

\[
x_v=\mathbf{1}_{v\in V(Q)},\qquad
e_v=\mathbf{1}_{v=q_{93}},\qquad
y_{uv}=x_ux_v.
\]

Both literal roots have even binary-weight parity. Every cube edge changes parity, so $q_{93}$ is odd and the 94 selected vertices split into 47 even and 47 odd vertices. The model has one endpoint variable for every allowed odd vertex, all 79 of them. The condition $\sum e_v=1$ leaves the second endpoint free. There is no endpoint variable at the even root, whose degree is separately fixed to one. All other even selected vertices are internal. The root is selected and has exactly one selected neighbour because any later selected neighbour would be a chord.

The round-218 exact-size equations are 47 selected vertices of each parity. The round-219 model deliberately retains only parity balance and maximizes total vertex selection. It therefore contains every actual 93-edge assignment. Its objective is $\sum_v x_v=94$ on such an assignment. The objective does not count endpoint or edge variables.

For a non-root vertex $v$, write $d_v=|N(v)|$ and $s_v=\sum_{u\in N(v)}x_u$, and set $e_v=0$ on even vertices. The saved vertex-degree rows are

\[
2x_v-s_v-e_v\le0,
\qquad
(d_v-2)x_v+s_v+e_v\le d_v.
\]

If $x_v=1$, these give $s_v+e_v=2$, exactly the internal/terminal degree rule. If $x_v=0$, then $e_v=0$ by endpoint selection and the rows reduce to $s_v\ge0$ and $s_v\le d_v$, which are automatic. They impose no unintended restriction on unselected vertices, including low-degree vertices.

The three product rows $y_{uv}\le x_u$, $y_{uv}\le x_v$, and $x_u+x_v-y_{uv}\le1$ are satisfied by the stated Boolean products. The edge-degree equations give degree one at the root and $2x_v-e_v$ elsewhere. They are also satisfied by every actual induced path. Omitting connectivity from the relaxation enlarges its feasible set and does not remove any path.

## Every saved row belongs to a necessary family

The read-only reconstruction reproduced all 1845 root-0 and 1840 root-78 original round-219 edge-model rows, including their literal indices, coefficient signs, senses, right-hand sides, and order. These equal the corresponding prefixes of the frozen long models. It then reconstructed every remaining row from the saved subset or parity witness, covering the entire suffix with no unclassified row.

| Root | Original rows | Occupancy squares / six-cycles | Forest rows | Square-parity rows | Longer parity rows | Total rows |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 1845 | 156 / 123 | 25 | 1248 | 27 | 3145 |
| 78 | 1840 | 154 / 120 | 30 | 1232 | 8 | 3110 |

Every saved occupancy set was checked to induce a connected cycle in the allowed graph. Selecting all vertices of a cycle would place that cycle in the graph induced by an actual path's vertices, which is impossible. Thus $\sum_{v\in C}x_v\le|C|-1$ is necessary. The frozen long-model lineage starts at the original round-219 edge model, then adds round-220 forest rows and round-221 parity rows; it does not inherit the separate round-219 dynamically separated-cycle model. This is harmless: omitting further necessary inequalities weakens the relaxation. The listed saved occupancy rows are all valid.

For each forest row, the marked vertex lies in the displayed subset $U$. The actual selected graph restricted to $U$ is a forest. If the marked vertex is selected, this forest is nonempty and has at most $X(U)-1$ edges; if it is unselected, the weaker bound $Y(U)\le X(U)$ suffices. Hence $Y(U)\le X(U)-x_v$ is necessary in both cases. The reconstruction included all induced edges within the subset and the cancellation of the marked vertex's coefficient.

Every square and longer parity witness is a simple allowed cycle with an odd edge subset $F$. For the actual Boolean products, $d_{uv}=x_u+x_v-2y_{uv}$ records whether the endpoint selections differ. A closed cycle has an even number of disagreements. Its pattern must differ from the odd pattern $F$ on at least one edge, yielding

\[
\sum_{e\in F}d_e-\sum_{e\in E(C)\setminus F}d_e\le |F|-1.
\]

This argument is valid for every Boolean selection, independently of path connectivity. The frozen coefficients were reconstructed by substituting the displayed disagreement expression. No inequality relies on an assumed numerical optimum or on floating separation having exhausted a family.

## Prefix equalities and exhaustive branching

For a prefix $(q_0,\ldots,q_k)$ of a hypothetical 93-edge path, all displayed vertices are selected. If $k<93$, every $q_i$ with $1\le i\le k$ is internal to the full path, including the last vertex of the partial prefix. Therefore imposing $x_{q_i}=1$ and, wherever the odd endpoint variable exists, $e_{q_i}=0$, is necessary. Calling the last prefix vertex an endpoint of the partial path does not make it the terminal vertex of the full path.

All observed prefixes have $k\le6<93$, so the nonterminal equalities are valid throughout this ledger. They would require reconsideration if the procedure reached a prefix of the full target length. Even prefix labels have no endpoint variable; the code only adds a zero equation when the corresponding `e<label>` exists. The root is already treated separately. The three inherited first-step exclusions use weaker models without these additional endpoint-zero equations, which is also safe.

The candidate rule admits every allowed neighbour of the current final vertex that has not already appeared and is not adjacent to an earlier prefix vertex. These are precisely the local distinctness and no-chord conditions required of the next vertex of any actual induced extension. The predicate uses the literal labels through XOR Hamming distance. It does not confuse prefix position with geometric coordinate or variable index. It may include candidates that cannot be completed, which only weakens pruning. At a depth below 93, absence of any candidate would validly exclude an extension, though the observed terminal ledger uses bound exclusions rather than such leaves.

To finish the exclusion, the separate ledger audit must establish that both seven-child first-step lists and every expanded child list are complete, that all descendants are present, that no unresolved node remains, and that each terminal exact bound is strictly below 94. The structural argument then follows an arbitrary actual path down its unique prefix branch and contradicts its 94 selected vertices at a terminal leaf.

## Exact scope of the resulting theorem

After the separate complete ledger and coefficient audit succeeds, the justified statement is: no induced 93-edge path in either allowed graph begins at its specified root. This excludes every compatible 93-edge partner of the saved parent, with its other endpoint unrestricted.

Any compatible path of at least 93 edges has a compatible induced 93-edge prefix beginning at the same root. Applying the exclusion to that prefix gives the bound of 92 edges for arbitrary partners, including even-length partners. This prefix step is essential because the frozen model itself describes odd-edge partners. Consequently every one-crossing join using the entire saved 98-edge parent has at most

\[
98+92+1=191
\]

edges. This is an upper bound for this parent and arrangement. It does not classify all 98-edge parents, cover multiple-crossing constructions, establish a global upper bound of 191, or improve the maintained global interval $191\le a(9)\le233$. Simultaneous cube isometries preserve the mathematical statement for copies of this same parent, but no new enumeration or Lean transport result is supplied here.

A bounded read-only lookup found the retained statement that earlier searches for 93-, 92-, and 91-edge partners at both endpoints were unresolved. No readily identified compatible 92-edge witness was verified in this review. Therefore this review does not assert attainment of 191 by this fixed-parent construction, nor that its maximum equals 191. The known global 191-edge witness is a separate fact.

The source-level necessity argument, generic Lean lemmas, native finite certificates, and global contributor theorem remain distinct. This review compiles no theorem, supplies no end-to-end Lean interpretation of the arrays or prefix tree, and does not independently rebuild the contributor 233 theorem.

## Evidence hashes

SHA-256 values identify the exact inspected inputs. Paths are relative to `E:/Snake-in-a-box`.

| Input | SHA-256 |
|---|---|
| `milestones/219-linear-partner/data/seed98.json` | `2b328e537867b097316150be170a9af68e5af492bc7667d3b781b77d39e4e2f5` |
| `milestones/219-linear-partner/scripts/linear_partner.py` | `4be866eb9b8764a5f756d36e1876ef866fa93fed0dd64c68dd445dea12c794fb` |
| `milestones/220-subset-forest/scripts/subset_separation.py` | `98d6ebf191e1acb9a059880f05c917fe70fe2effc350f2d37fa288eeb36f2113` |
| `milestones/221-square-parity/scripts/square_separation.py` | `91f5da0c935078b8c12ca20388abd6389524d2f1a01bb0fd4c3e7160a18c7335` |
| `milestones/221-square-parity/scripts/long_separation.py` | `fda3d5718fe61c27cddc47430e16b610df821a12c6d1bc91a7f6954cce98e365` |
| `milestones/221-square-parity/data/long-0/model.json` | `a4f0aa53fe7a8c06969643cd7a5b09c50459d6d5013e6568708b42a8ad76ce67` |
| `milestones/221-square-parity/data/long-78/model.json` | `d0151302ca6cc914f5331befb72dcd00f22e9c0b06c46cc25da8efa8e8896dd3` |
| `milestones/222-prefix-certificates/scripts/prefix_search.py` | `a337d739bcf179f6565e76166cf52df85558979a4a45456bf4eef1e4aa6dc873` |
| `milestones/222-prefix-certificates/scripts/prefix_continue.py` | `63e855618b414ee411c43bb7359b7d1fa4d4e362dddfec3d72b50ce2cecdc916` |
| `milestones/222-prefix-certificates/scripts/prefix_deep.py` | `2d0a90a81d80c0c9c1b4b24c95494dc48ddabb76b882b588ab3d363ff764b09e` |
| `milestones/222-prefix-certificates/data/deep-ledger.json` | `58c66c01369e5108a6b411268668d70a078d2e2b83cf41a1bbb631e65248a0c8` |
