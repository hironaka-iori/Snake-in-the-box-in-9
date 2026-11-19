# Round 243. Opening the 192-vertex coil in nine dimensions

The direct target is an induced path on 193 distinct vertices of \(Q_9\). The construction source is the nine-dimensional 192-vertex induced cycle in the authors' record data. The [local entry](coil9.json) records its transition sequence, ordered vertices and upstream revision. Before each search, the cycle is checked for distinct vertices, consecutive adjacency including the closing edge, and absence of all other adjacencies. The verified symmetries used here are the identity and a half-turn by 96 positions. For each possible offset and orientation the program checks consistency of the full coordinate permutation along the ordered cycle. [Primary data at the inspected revision](https://github.com/Math-AI-Caltech/Snake-in-the-Box/blob/46c765399353a588ea50444a5d6610f53102b1c2/record_coils.csv) · [Orland et al.](https://arxiv.org/abs/2607.15270)

## Exact two-ended search

Retain \(s\) consecutive vertices of the coil in order. A path containing them as a contiguous segment consists of this arc, a left tail and a right tail. Either tail may be empty. Its first vertex may touch the corresponding endpoint of the arc; subsequent vertices must avoid the entire closed neighbourhood of the arc. Internal and cross-tail nonconsecutive contacts are forbidden. Vertices in the original omitted portion may be reused. Thus the search includes changes to both parity classes and both endpoints.

The [enumerator](open_coil.py) considers every stop or continuation of the left tail and enumerates each permissible right tail at that stopping point. After appending vertex \(v\), it makes all of \(N[v]\) unavailable to later nonconsecutive steps, while allowing the *immediately following* vertex from the former available neighbours of \(v\). When building the left tail it also removes \(N[v]\) from the possible first right vertices. This enumerates all ordered tails consistent with the fixed arc. An accepted 193-vertex sequence must pass a separate all-pairs adjacency check. A node limit applies to each representative; it gives an unfinished status if the tree is interrupted.

For \(s=160\), all 96 representative trees were exhausted in 2,946,409 nodes. The longest result had 192 vertices (191 edges). The earlier limited batch had two unfinished trees and is retained separately. Thus no 192-edge snake contains a 160-vertex arc of this particular coil or a cube-isometric copy.

At \(s=148\), 71 representative trees were exhausted and 25 reached their node limit. Together they explored 97,803,611 nodes. The largest generated path again had 192 vertices. [Complete 160-vertex arc census](arc-160-5000000.json) · [148-vertex arc census](arc-148-2500000.json)

## Simultaneous choice of both tails

The [second search](arc_sat.py) retains the same fixed arc and allows all its two-ended continuations. Vertices adjacent to an interior arc vertex are forbidden. An external vertex adjacent to both arc endpoints would close a cycle, so it too is forbidden. Only components reachable from an endpoint are retained. For a proposed 193-vertex selection, every selected vertex must have induced degree two, except for exactly two endpoints of degree one. The fixed interior vertices already have degree two; both arc endpoints remain free to become global endpoints. Unselected vertices have no degree requirement. Cardinality bounds use the binary totalizer construction.

A satisfying degree assignment may contain disjoint cycles. The program recomputes the induced graph from vertex labels, discards such assignments with a cut forbidding all the vertices of each cycle from being selected together, and repeats under the per-query time limit. Each cut is necessary because retaining the entire induced cycle is impossible in a path. A connected assignment is ordered and checked on every pair. Native solver contradictions apply only to the specified fixed arc; a timeout supplies no exclusion.

At 148 retained vertices the simultaneous selection model returned UNSAT for each of the 25 unfinished representatives. At 112 retained vertices it excluded 57 of 96 representatives and timed out on 39. Every arc containing an excluded shorter arc inherits its exclusion. This covered 158 of the 192 starting positions at length 128. All 17 remaining representative queries (34 positions) returned UNSAT. Thus no 192-edge path can retain a contiguous arc of 128 vertices from this coil. These statements combine elementary containment with native finite solver outcomes. There is no Lean replay of these contradictions. [148-vertex results](sat-148-1.5.json) · [112-vertex results](sat-112-1.5.json) · [128-vertex results](sat-128-3.json)

At 120 vertices the 112-vertex results already exclude 142 starting positions. Of the remaining 25 representatives, 23 were excluded and two timed out (starts 86 and 88 and their half-turn images 182 and 184). These four unresolved positions are pairwise nonconsecutive around the cycle. Every 121-vertex arc contains two adjacent 120-vertex subarcs, at least one of which is excluded. **No 192-edge snake can contain a contiguous 121-vertex arc of this coil, up to cube isometry and reversal.** The four 120-vertex positions remain unresolved at the recorded cutoff. The process resumed completed queries after the memory reserve interrupted a run. [120-vertex runs and inherited positions](sat-120-4.json)

## Opening the coil without retaining an arc

Fix one parity class of the coil as the target's 96-vertex minority, or exchange one of its 96 vertices for one of the 160 other vertices of the same parity. The 97 majority vertices, ordering and endpoints are all free. This gives 15,361 configurations on each parity side. For each, use the [fixed-minority contraction criterion](../232-minority-contraction/MATHEMATICAL_NOTE.md). Add a dummy vertex adjacent to every eligible endpoint. A Hamiltonian cycle of the resulting simple graph is necessary and sufficient. After success, labels would be selected on its edges and at its two ends, and the entire cube sequence checked directly.

| Obstruction | Even minority | Odd minority |
|---|---:|---:|
| Isolated minority vertex | 8,728 | 13,506 |
| Leaf obstruction | 6,616 | 1,842 |
| Fewer than two eligible endpoints | 0 | 6 |
| Contradiction from forcing degree two | 12 | 7 |
| Native solver contradiction | 5 | 0 |
| Total | 15,361 | 15,361 |

To force degree two, retain all remaining incident edges when exactly that many are needed and discard all others once two edges are fixed. Contradictions arise if too few or too many edges can remain. The five residual circuit decisions used exact degree-two constraints and cuts requiring an edge to leave each proper circuit component. The native finite calculation excluded every case. In particular any 192-edge path must omit at least two vertices of its 96-vertex minority from the corresponding coil class and add at least two others. There is no restriction on the other parity side in this statement. [Search and certificate logic](coil_exchanges.py) · [Outcomes](coil-exchanges.json)

## What the best arc openings produced

As a separate construction check we collected the 191-edge paths from all 160-vertex arc representatives. The enumeration reverses the retained arc. Its search terminates when the tails contain 32 vertices in total. It found 1,030 placements across the 96 representatives, giving 49 distinct cube-isometry classes up to path reversal. Each first representative was verified on all vertex pairs. Every class belongs to the published bank. Thus this long-arc route supplied neither a new 191-edge starting class nor a verified 192-edge path.

The normalization renames transition coordinates by their order of first occurrence and takes the lesser of the forward and reversed words. Equality of normalized words gives a coordinate permutation taking one transition sequence to the other, with translation aligning the starting vertex. Every cube isometry and path reversal preserves that key. The receipt includes a full path for every class. [Census](census191.py) · [Verified paths](record-census.json)

The next construction source is the separate published collection of 190-edge paths. These permit a different 96-vertex minority class for the 192-edge target, with all 97 majority vertices and their order free. The maintained project interval is \(191\le a(9)\le231\). Its upper endpoint is the contributor's completed theorem with an independent full rebuild pending. The present work concerns constructions in \(Q_9\).
