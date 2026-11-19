# Round 245. Reconstruction from 190-edge parents with both endpoints free

Can a 192-edge path in \(Q_9\) retain an entire parity class of a recorded 190-edge path when the parity of its endpoints is unchanged? Can it retain 190 of the parent's 191 vertices if its endpoints have either parity? Both questions have negative answers for all 1,042 parents in the source collection. A target must omit at least two parent vertices and introduce at least four. If its endpoints have the same parity as the parent's endpoints, it must omit at least one vertex of each parity.

The input is the member named snakes_dim9_190.csv of the authors' public archive, with SHA-256 digest 86402090cffaca74d2402152b382248ba71819af89497e7e1c8f792fa395f74f. Round 244 checked all input path orders and identified 1,042 distinct classes under cube isometries and reversal. An isometry applied to both paths preserves every conclusion below. [Primary paper](https://arxiv.org/abs/2607.15270) · [Archive at the inspected revision](https://github.com/Math-AI-Caltech/Snake-in-the-Box/blob/46c765399353a588ea50444a5d6610f53102b1c2/record_snakes.csv.zip) · [Round 244](../244-190-path-construction/README.md)

## Retaining either parity class

A 190-edge parent has 96 vertices of its endpoint parity and 95 of the other parity. The corresponding sizes of a 192-edge target are 97 and 96. When endpoint parity agrees, retaining one whole parent class specifies a target class \(S\) by one addition. Both target endpoints, the order, and the entire opposite class are free.

On \(S\), join a pair when some cube vertex off that parity has precisely those two neighbours in \(S\). For a fixed 97-set, seek a Hamiltonian path in this graph. For a fixed 96-set, each end of that path must additionally have an opposite-side vertex whose only neighbour in \(S\) is that end. These requirements are sufficient as well as necessary. Choose one opposite-side label per traversed pair. A label cannot serve two different pairs. The singleton labels required for the 96-set are distinct and unused inside the path. Vertices on the same parity cannot introduce chords. Interleaving the labels therefore constructs the full 193-vertex target.

Connect a dummy vertex to every eligible endpoint and require a connected cycle with degree two everywhere. The following counts refer to distinct enlarged sets after identifying duplicate descriptions. There are \(588\cdot160=94\,080\) descriptions of 97-sets and \(581\cdot161=93\,541\) descriptions of 96-sets. [Enumeration](reconstruct.py) · [Per-parent results and solver inputs](results.json) · [Execution receipt](reconstruct-receipt.json)

| Reason for exclusion | Fixed 97-set | Fixed 96-set |
|---|---:|---:|
| Isolated vertex | 69,931 | 65,644 |
| Fewer than two eligible endpoints | 0 | 47 |
| Incompatible degree-one vertices | 23,580 | 27,230 |
| Disconnected graph before degree propagation | 0 | 5 |
| Contradiction in forced degrees | 90 | 133 |
| Remaining cases with saved exclusion trees | 2 | 58 |
| **Distinct sets** | **93,603** | **93,117** |

All cases were decided. The original calculation used CaDiCaL for the last 60 sets. A second calculation rebuilt their graphs directly from bit flips and recorded graph-theoretic exclusion trees without using the solver. Start with all edges available. A vertex with only two available edges requires both. A vertex with two required edges forbids its other edges. Fewer than two available edges, more than two required edges, a disconnected available graph, or a proper cycle of required edges excludes a completion. At each branch, one child includes the specified edge and the other excludes it. The 60 trees contain 270 branch positions and 330 terminal contradictions. The dummy vertex is numbered 512. [Trees](degree-proofs.json) · [Independent construction](degree_proofs.py) · [Execution receipt](degree_proofs-receipt.json)

On each parity side the indicator difference has sum one. The rank-nine moment identity gives at least nine changed neighbour counts. Equality would mean adding just one vertex to that class, which the enumeration excludes. The written growing-side result excludes ten for any ternary difference of sum one. Thus each side changes at least eleven counts. They are counted on disjoint parities, so at least **22 labelled neighbour counts** change when endpoint parity agrees. Round 244 gives **20** when it differs. These are necessary conditions measured against each recorded parent. [Round 241](../241-exact-count-distance/README.md) · [Round 242](../242-seed-trade-construction/README.md)

## Retaining all but one vertex, in either orientation

Deleting one of a parent's 191 vertices leaves 190 vertices in one or two components. In any induced completion, every edge of each remaining component persists, so each component must occur as a contiguous block. There are three new vertices available at the target length. If there are two components, choose the orientation of each, hold their order fixed by whole-path reversal, and enumerate every bridge with one, two, or three new vertices. Each interior bridge vertex can have only its designated neighbours among vertices already present. After joining, distribute the remaining vertices between the two outer ends. For a single component only the outer extensions are needed. The deleted vertex is forbidden throughout. Keeping all 191 original vertices was covered separately by Round 244's exhaustive two-step extensions.

| Best connected length with exactly this deletion and up to three additions | Parent and deletion choices |
|---|---:|
| No connected completion within that allowance | 175,612 |
| 189 edges | 1,539 |
| 190 edges | 18,352 |
| 191 edges | 3,519 |
| 192 edges | 0 |
| **Total** | **199,022** |

Each choice consists of one parent and one deleted index. Different choices can produce the same path. For each recorded parent \(P\) and each 192-edge target \(T\), this finite enumeration gives \(\lvert P\cap T\rvert\le189\). Consequently \(\lvert P\setminus T\rvert\ge2\) and \(\lvert T\setminus P\rvert\ge4\). This statement allows arbitrary endpoint parity. [Direct enumeration](one_loss.py) · [Per-parent counts](one-loss.json) · [Execution receipt](one_loss-receipt.json)

## Evidence and next decision

The equivalence with a Hamiltonian path and the deductions about counts and overlap are written arguments. The family coverage and the exclusion trees are native finite evidence. This round produced no new Lean theorem. The reviewed global interval is \(191\le a(9)\le231\), and the exact maximum and the proposed value 196 remain open. The contributor's upper-bound assembly has a saved passing audit at revision 478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088. An independent full dependency rebuild remains pending.

The project pauses after this round. On resumption, one direct construction to try is to omit one vertex of each parity from a 190-edge parent and reconnect the remaining components with four new vertices. This is the smallest exchange left open by these two searches when the endpoint parity is preserved. The next full written-source review is due at Round 250.
