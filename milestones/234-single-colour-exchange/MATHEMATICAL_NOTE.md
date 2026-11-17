# Round 234: replacing one member of a parity class

The construction hypothesis was that one replacement in a saved 96-vertex minority class could support a 192-edge snake, with the opposite parity class, endpoints and ordering unrestricted. The finite cover excludes this family under the evidence described below. It does not exclude 192-edge snakes generally.

## Exact update

For a selected class U, remove d in U and insert a same-parity vertex a outside U. Write U'=(U minus {d}) union {a}. For every opposite-parity label z, its selected neighbours become its old selected neighbours with d removed, together with a exactly when z is adjacent to a. Hence its complete neighbour set is unchanged exactly when z sees neither exchanged vertex.

A label adjacent to both d and a keeps its degree but changes its neighbours. It cannot be left unchanged in an edge cache. A singleton label can arise from an old degree-zero label after insertion or an old degree-two label after deletion. A new internal degree-two label can arise from an old degree-one or degree-three label. The enumeration must include labels that were previously unusable.

ColourExchange234 has four accepted Lean statements for the exact update, the unchanged-neighbour-set equivalence, and the singleton and pair specializations. They are general relational statements. The numerical degree equation and the finite cube implementation remain separate written and computational arguments.

## Complete construction family

The input contains 145 distinct labelled parity classes from 131 saved 191-edge snakes. Each has 96 vertices. There are 96 possible removals and 160 outside same-parity insertions per class, totalling 2,227,200 descriptions. Resulting sets can coincide across descriptions. The static scan processes all descriptions and deduplicates only survivors by exact equality of the complete selected set.

For each resulting class, labels with exactly two selected neighbours form internal graph edges. Labels with exactly one selected neighbour allow endpoints. The accepted minority-class criterion says that a Hamiltonian path in the internal graph with supported endpoints gives exactly 192 edges; conversely every snake with that minority class supplies such a path.

The static decisions are 1,603,284 isolated-vertex exclusions, 616,230 cases with too many leaves, 274 with fewer than two supported endpoints, 6,019 with an unsupported leaf, and 12 disconnected cases. The remaining 1,381 descriptions represent 1,325 distinct classes. The independent audit reconstructed every complete resulting class directly, without using the producer's incremental graph updates, and accepted all 2,227,200 decisions. The final coverage audit also accepted all 1,325 graphs, all 793 exported native models, and the union of elementary and native exclusions.

## Elementary contradictions and remaining native evidence

Add a dummy vertex joined to every supported endpoint. A Hamiltonian path with supported ends exists exactly when this augmented graph has a spanning cycle. Every vertex on such a cycle has two used edges. Therefore both edges at an available degree-two vertex are forced; once two incident edges are forced, all other edges at that vertex are excluded. Repeat these deductions until either they stop or a contradiction occurs.

The contradictions used are an available degree below two, more than two forced edges at a vertex, a forced cycle on a proper subset of vertices, or deletion of one vertex leaving multiple graph components. The latter contradicts the connected path left when a vertex is deleted from a spanning cycle. It is valid even when the reduced graph was already disconnected.

Exactly 1,244 of the 1,325 classes have such certificates, all independently replayed from their literal cube neighbourhoods. The remaining 81 have native circuit infeasibility evidence. The first native batch completed 771 infeasible queries before its time limit; the unfinished suffix was not classified from that limit. After using the elementary certificates, only 22 uncovered classes remained. A second batch excluded all 22. The full union covers every surviving class, with 81 classes depending on native contradictions and no unresolved class.

The elementary traces are independently checked finite certificates with written justification. They are not Lean certificate replays. The native infeasibility conclusions retain their solver scope. No new path longer than 191 edges was found.

## Consequences for the next construction

For any proposed 192-edge snake and any saved seed, its 96-vertex minority class contains at most 94 vertices of the corresponding 96-vertex seed class. An intersection of 96 is the already excluded fixed-class case; an intersection of 95 is exactly one replacement and is excluded here. Round 231 also limits the 97-vertex majority class to at most 95 vertices of the other seed class. Consequently the proposed snake can share at most 189 of the seed's 192 vertices. It must omit at least three old vertices and introduce at least four new ones.

This conclusion transports to cube-isometric copies of each saved seed by applying the inverse automorphism to the proposed snake. It depends on the stated finite covers. It does not assert that removing three old vertices is sufficient.

There is also an exact restricted maximum: if one complete selected parity class has 96 vertices and differs from a saved class by at most one replacement, alternation bounds the edge length by 192. The 192-edge case is excluded, so the length is at most 191. An original seed attains 191 in the zero-replacement part of this family. This is not a global upper bound.

The next constructive experiment allows two replacements in a saved minority class and chooses its opposite class and ordering jointly. NEXT_CONSTRUCTION.md describes an optional-vertex circuit model to avoid explicit enumeration of billions of descriptions. It remains unexecuted at this checkpoint. Partial greedy growth is reserved for cases where it helps generate candidates.

The maintained global interval remains 191<=a(9)<=233, with a fresh independent rebuild of the contributor's 233 theorem pending. The 196 conjecture remains unresolved. The user resumed the goal after round 233; the goal remains active.
