# Round 195: dimensional patterns and symmetric path forests

The construction goal remains active. The user redirected this round towards patterns in the 6-to-7 and 7-to-8 constructions. No new Q9 record or upper bound was obtained. The new useful result is a precise construction family and its checked lifting argument.

## What transfers between dimensions

The displayed Q7 snake has the decomposition 18+24+6+2=50. The prior comparison showed that its 24-edge Q6 middle is more useful than the displayed optimal 26-edge middle, whose best compatible two-crossing lift has 48 edges. Compatibility must be optimized jointly.

The displayed Q8 snake has the decomposition 8+25+10+25+26+4=98. One face contains two 25-edge paths, hence 52 vertices; the opposite face contains three paths with 47 vertices. A single longest Q7 snake has 51 vertices, so allowing two components increases the useful face occupancy.

For Q9, use two nonadjacent paths in one Q8 face and three in the other. The vertex sets A and B must intersect exactly in four crossing ports. All four ports are endpoints of the two A paths, and have B-degree at most one. The graph joining the five face components through the four ports must be connected. Then all full-graph degrees are at most two and the edge count is (|A|-2)+(|B|-3)+4=|A|+|B|-1; connectivity forces one induced path. Equivalently, the B components contain1,2,1 ports, with the two-port component joining different A components. Singleton outer B paths are allowed. Connectivity cannot be omitted: a cycle plus a path can satisfy the degree and edge counts.

A useful provisional target is two 49-edge A paths, using 100 vertices, together with 95 compatible B vertices. This would give 194 edges. A 97-vertex B forest would give 196. These are construction targets, with neither existence nor optimality established. Base Hamming parity reverses in the other face: the full colour difference is the A difference minus the B difference. Two 49-edge A paths are balanced; a 194-edge construction therefore needs B colour difference plus or minus one.

## The observed symmetry

With coordinate indices 0 through 6, the two 25-edge Q7 components are exchanged by g(x)=sigma(x) xor73, where sigma swaps coordinates 2 and 5, and 73 flips coordinates 0,3 and 6. This is an involution. Its paired vertices have Hamming distance 3 or 5. Extend g to Q8 by leaving coordinate 7 unchanged.

Identify each vertex with its partner under g. The resulting graphs have 64 vertices in the first case and 128 in the extension; adjacency means that at least one cube edge joins the two pairs. The 128-vertex graph is the Cartesian product of the 64-vertex graph and one binary edge.

An induced path in this quotient lifts to two disjoint nonadjacent induced paths in Q8. Choose the first representative; each step then has a unique neighbouring representative. Uniqueness follows because two representatives of one orbit have distance at least three and therefore cannot share a cube neighbour. Distinct quotient vertices prevent intersection of the two lifted paths. A contact between nonconsecutive lifted vertices would project to a quotient chord. A contact between consecutive vertices of different lifts would give two possible lifts of one edge, already excluded. Contacts within one orbit are excluded by the same distance condition.

Lean checks the generic path-lifting and separation implications, transport under an involution, and all 256 values of this specific involution. Eight further chunks check every cube-neighbour image and the absence of common cube neighbours of paired vertices. These proofs do not certify the numerical search census or the complete solver encoding.

## Restricted construction and the Q9 comparison

All 1536 specified commuting isometries were used to place a second copy of the observed 25-edge quotient path. All choices of one contiguous subpath in each face, with one crossing, were considered. The maximum within this family is 42 edges. The corresponding Q8 pair has two 43-vertex paths,86 vertices total, and was independently checked for all pairwise adjacencies and cross-contacts. This is a restricted native maximum, not the unrestricted quotient optimum.

Among the 36 distinct labelled four-crossing fixed forests extracted from the saved Q9 bank, one uses 98 vertices and 35 use 96. Twenty transition-determined isometries exchange balanced 47-edge component pairs. Seventeen use two coordinate transpositions and two fixed coordinate flips; three use three transpositions and two fixed flips. None belongs to the directly matched one-transposition, three-fixed-flip class of the Q8 example. This is a comparison of the enumerated labelled maps, not a classification of all forest symmetries.

The first observed 47-edge pair has an involution with minimum partner distance two. Some quotient edges then lift to a square. Such an edge cannot be used in a pair of nonadjacent paths, and selecting its two quotient endpoints is forbidden. It is insufficient merely to delete the quotient edge, since that would hide a real cross-path contact. A second Lean separation lemma requires uniqueness only on the chosen consecutive steps, covering this more general construction principle under explicit premises.

## Computations and limitations

The connected-flow quotient search for 50 vertices under the extended Q8-example symmetry remained UNKNOWN after 120 seconds. The query using the first saved 47-edge pair, seeking 50 quotient vertices with at most four omitted original orbits and one fixed endpoint, remained UNKNOWN after 90 seconds. Four omitted orbits mean at most eight omitted vertices from the 96-vertex paired forest; they do not bound omissions from each individually labelled component by four.

The four-crossing completion with the 98-vertex fixed bank face and target 192 edges remained UNKNOWN after 120 seconds. The variable opposite-face lower-dimensional query targeting 98 also remained UNKNOWN after 30 seconds. With both face selections fixed to the known examples, the same contraction-and-flow model reconstructs the 98-edge Q8 and 191-edge Q9 snakes, and both decoded paths pass all-pairs checks. These reconstructions establish feasibility of the stated patterns. They do not establish an optimum or resolve the larger queries.

The earlier short-state search stopped at the 768MiB free-memory reserve after completing six states and discovering 238 states. It established no complete closure and found no longer witness. Its exact source is preserved. The source's overly frequent resource sampling was corrected afterwards without rerunning that branch; all incomplete coverage remains unresolved.

## Next step

Continue from the observed 47-edge paired forest, using its safe quotient edges. Replace the expensive connectivity-flow search by the induced-degree relaxation and exclude disconnected cycles when they appear; each such exclusion is sound because a cycle cannot be a selected subset of an induced path. Keep an explicit omitted-orbit bound initially, then widen it if the restricted query is excluded. A valid 50-vertex quotient path would give a 100-vertex two-path face; its remaining three-path completion must still be solved. The separate four-crossing completion can vary the ports and fixed face instead of repeating the unchanged timeout.

There is no novelty claim for quotient lifting, graph contraction, or path-forest gluing. The specific observed symmetries and their usefulness for this construction are the research findings of this round. The archived 235 upper-bound rebuild and conditional 233/234 dependencies are unchanged. The next whole-manuscript review remains round 200.

Final contributor refresh: branch advanced to dfa35ffd592587f62125cf7b4871cbd9e04c3c0f, adding ten production/replay data lines in two files. The diff is saved in milestone195 data/contributor-final.diff; it was neither merged nor independently rebuilt.
