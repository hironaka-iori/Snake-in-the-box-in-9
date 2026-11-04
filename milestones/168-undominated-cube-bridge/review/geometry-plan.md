# Cube interpretation of milestone 167

Source: lean/CubeUndominated168.lean. Namespace: Snake9.Undominated168.

Status: drafted, not compiler-checked by this worker. The coordinating agent owns all compiler invocations and acceptance decisions.

The hypotheses are an actual Snake9.Snake m with m >= 1, and absence of every unit vertex from the selected path. The latter expresses that zero has no selected neighbor. No axiom asserts the abstract pair/triple interpretation.

1. selected_neighbor: a selected path vertex has a selected neighbor, using its successor unless it is the final index, and its predecessor otherwise.
2. selected_triple_distinct: a selected triple cannot repeat either first coordinate in its third position, since the triple would cancel to an absent unit vertex.
3. minimum_pair_neighbor: every selected pair has a selected triple neighbor whose third coordinate differs from the pair coordinates.
4. maximum_triple_neighbors: a selected triple cannot have its three distinct pair-side vertices selected, since an induced path has degree at most two.
5. no_two_unused_directions: the actual pair/triple interpretation now instantiates milestone 167. Two directions whose incident pair vertices are all selected are impossible.
6. matching_pair_low_degree: given an unused direction c and a direction a with at most one absent incident pair, every selected neighbor of pair(c,a) is its prescribed triple. Thus pair(c,a) is selected and has at most one selected neighbor.
7. three_matching_pairs_impossible: three distinct pairs forced to have this property contradict the existing path endpoint theorem. This avoids counting eight endpoints in the geometric bridge.

No claim is made here that the absent-pair graph has at least five edges: the finite counting bridge from at most four absent pairs to an unused direction and matching partners remains a separate dependency. Translation from zero to an arbitrary cube vertex remains separate as well. A global empty-square loss statement additionally requires the sum of local losses and the incidence identity.

The source imports CubeLocal and Undominated167, uses no new axioms, sorry, admit, or native_decide, and does not modify any preceding milestone.
