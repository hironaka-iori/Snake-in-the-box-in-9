# Round189: restrictions on replacing the common95-edge component

The goal remains active. The user requested relations6→7,7→8,8→9; this round follows the95→97 replacement target from round188. No longer snake or improved global upper bound was found.

## Mathematical content

The observed family47,95,191 has48,96,192 selected vertices. The relations95=31+47+15+2 and191=95+94+2 balance the selected vertices across both faces. This is an observed family, not a universal doubling construction.

The exact joining rule gives31+49+15+2=97 and, with compatible outer paths totalling94, gives193. NestedReplacement189 checks these conditional implications. The existence of the49/97 paths with the required compatibility is unproved.

The overlap-repair inequality is |A∩B|≤|A\A'|+|B\B'| whenever A',B' are disjoint. Omit designated crossing ports from the ground set. Each original overlap must be removed from at least one set. ReplacementBudget189 checks the counting proof, including the fixed-outer case. It does not check the entire placement enumeration.

## Finite evidence

1. All84contexts for the common95 type leave162 allowed Q8 vertices. Leaf pruning and the block-cut route remove none. The first fixed-port97 search is UNKNOWN at120.062seconds. Context canonicalization concerns the original path together with its allowed set, not the bare allowed graph with ports.
2. Nested47→49 replacement leaves64–72 allowed Q7vertices. In context0 it is INFEASIBLE in1.593seconds. Removing all externalQ9restrictions leaves82 vertices and is INFEASIBLE in114.375seconds. This excludes changing only the47 piece while retaining the31/15 pieces and ports; it is not a globalQ8 orQ9 result. The nested allowed sets were independently reproduced after a read-only model review.
3. All1440 endpoint-preserving placements of the applicable97-edge truncation of the displayed98-edge snake have≥23 forbidden overlaps across all84contexts. Minima distribution23:7,24:33,25:36,26:8. All960 placements of the49-edge truncations of the displayed50-edge snake have≥11 overlaps; distribution11:34,12:30,13:17,14:3. These classify only the stated seed placements. The general repair inequality implies corresponding minimum total removals before compatibility can hold.
4. Contiguous local replacement: all3087 intervals of1–42 internal vertices are exhausted with no97-edge replacement, even without externalQ9constraints. Size43 has23 completed intervals and a partial next interval; the120second run ended incomplete. No universal size43 exclusion. The unchanged path outside the interval retains its order. This is not a lower bound of43 omitted vertices.
5. Two separated changes: all4278 pairs of nonadjacent internal positions, both orientations of the retained middle chain, and every connector-length pair(2,4),(3,3),(4,2) are enumerated. No replacement exists in this finite search. Three retained chains force this decomposition: the endpoint chains are fixed, the middle can reverse, and the two connectors must total six edges. Their endpoints were nonconsecutive in the original induced path, so neither connector can have length one. Adjacent and single changes were covered by contiguous sizes1/2. Keeping every original vertex cannot lengthen a fixed-endpoint induced path because its original edges are forced.
6. A generalQ8 circuit model retaining exactly93/96 original vertices reports INFEASIBLE in28.641seconds. It includes all outside cube vertices and does not impose anyQ9outer restrictions. The exact-four-omission model reports INFEASIBLE in80.563seconds. Thus the current computational minimum is5 omissions and7 additions for a97-edge fixed-port replacement. The solver exclusions have no Lean contradiction certificates.

## Search-model argument

Binary vertex variables choose the path. Each physical cube edge between two selected vertices must be used as a directed circuit arc in one direction. A mandatory virtual arc from the terminal port to the initial port closes the desired path. Self-loops mark unselected vertices. The single-circuit constraint excludes disconnected cycles; the forced physical arcs exclude chords. Ports have Hamming distance3 (or5 in the nested problem), so the virtual arc is not a physical cube edge. Every returned feasible path would be decoded and checked pairwise. No feasible longer path was returned.

The native depth-first enumeration forbids every new interior vertex that meets a retained vertex other than its connection endpoints, and excludes chords to earlier new vertices and premature adjacency to the terminal endpoint. It considers all remaining cube neighbours. Distance pruning is a necessary condition only. Its complete ranges and partial stopping point are recorded separately.

## Next action

Search a97-edge replacement with exactly five original vertices omitted, or vary the crossing ports and neighbouring components. The cases with up to four omissions are computationally excluded, with the three/four cases lacking Lean contradiction certificates.

Consider changes spread across several components: retaining the31/15 pieces already blocks the nested improvement, and every single interval through size42 is excluded. The evidence does not exclude a97-edge path with the same ports after larger coordinated changes, a different port pair, or different surrounding paths. The194 target remains provisional and196 remains unresolved.

## Verification and preservation

Four local modules have accepted receipts: two reused joining-support modules and two new modules for overlap repair and nested conditional construction. All source, object, log and dependency hashes were rechecked. Standard Lean axioms only; no admitted proof. These checks do not establish the finite solver exclusions. The pending round188 directQ8 pairwise recheck is preserved unchanged. No proof or search worker remains active at closure.

Round187 upper-bound state is preserved:93/98 clause batches, conditional233/234, and archived235 awaiting complete independent rebuild. No contribution branch was merged. The fetched contributor head remainsf393c48e. The manuscript-wide review remains pending. ExistingD: manuscripts andE: mirrors preserve authors and hypersetup.
