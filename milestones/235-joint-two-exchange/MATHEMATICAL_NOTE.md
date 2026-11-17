# Round 235: joint construction and the two-replacement obstruction

The hypothesis was that replacing two vertices of a saved 96-vertex minority parity class could yield a 192-edge snake when the entire opposite class and ordering were chosen jointly. A complete necessary-degree cover excludes this family for all 145 saved classes. The exclusions are native solver results supported by independently reconstructed models; they are not Lean contradiction certificates. No new Q9 record or global upper bound is obtained.

## Exact circuit formulation

Select 96 minority and 97 majority vertices of the actual Q9. A saved minority class U has 96 vertices; requiring exactly 94 selected vertices from U specifies two removals and two insertions. For every cube edge vw, use two directed arc indicators f and b, with f+b<=x_v, f+b<=x_w and f+b>=x_v+x_w-1. For Boolean selections these mean f+b=x_v*x_w: every selected cube adjacency must be used, and an edge incident with an unselected vertex cannot be used.

An unselected vertex takes a self-loop; a selected one cannot. A dummy is joined only to selected majority vertices and has no self-loop. One circuit through the dummy and all selected vertices becomes a path after deleting the dummy. Exactly 193 cube vertices are selected. Cube two-cycles are forbidden by f+b<=1, and a dummy two-cycle cannot contain the other selected vertices. Conversely, every target induced path gives a satisfying orientation. There are no quotient, endpoint-order, crossing or fixed-opposite-class restrictions.

Four independent queries for classes 139, 7, 6 and 0 each returned UNKNOWN after 60 seconds. They establish no exclusion. The exported 5,632-variable, 7,428-constraint models were independently audited. Class choice was heuristic, based partly on survivors from round 234; it was not a symmetry cover.

CircuitPath235 has four accepted Lean statements: the Boolean edge identity, its exactly-one-direction consequence, injectivity from exact successor-arc correspondence, and construction of an actual induced path from supported arcs, adjacency coverage and successor order. Extracting the full selected order from the solver's unique circuit and supplying literal cube inputs remain separate bridges.

## A smaller necessary degree model

Let x_v indicate selection and let e_v indicate an endpoint on the majority parity class, with e_v=0 on the minority class. Require exactly two endpoint flags and e_v<=x_v. For every selected vertex require that the number of its selected cube neighbours is 2-e_v. For unselected vertices impose no degree restriction.

These equations preserve every target snake. The selected graph has exactly two degree-one vertices and all other vertices have degree two. It is therefore one path, joining the two endpoints, together with zero or more disjoint cycles. Connectivity is deliberately left open at this stage.

A disconnected feasible selection would yield a valid cut excluding full occupancy of each cycle. Changing other selected vertices cannot remove the cycle's ambient edges from an induced graph. The accepted Cycle218.cycle_cut theorem supports this principle, subject to checking the actual distinct cycle and its cube edges. Degree219.selected_degree_iff supplies a checked alternative signed encoding of the conditional selected-degree equation. Their source, object, compiler log and dependency hashes were rechecked; neither older module was rebuilt in this round.

The implementation supports cycle separation and complete all-pairs validation of a connected candidate. No cycle cut was needed in the present runs.

## Complete result and evidence

The first four degree queries returned INFEASIBLE in approximately 0.25--0.45 seconds each. A separate batch covered the other 141 classes. All 145 were natively infeasible in their initial degree model. Each model has 768 Boolean variables and 772 constraints: four cardinality equations, 256 endpoint-selection inequalities, and 512 degree equations enforced by the positive selection literal.

The independent audit verified every variable, every constraint and enforcement literal, all result and source pins, and complete coverage of class IDs 0 through 144. There are no unqueried or unresolved classes in this exact-two-replacement cover. It represents 145*binomial(96,2)*binomial(160,2)=8,410,464,000 exchange descriptions before duplicate sets, without enumerating each description individually.

The native exclusions occur in the degree relaxation itself. Thus the obstruction already prevents choosing 193 vertices with the required induced degrees; it does not depend on finding their order, imposing connectivity, or banning cycles. This conclusion is restricted to two replacements from the saved classes. The four earlier UNKNOWN circuit results remain unchanged in the evidence.

## Stronger distance from saved seeds

For any proposed 192-edge snake, its minority class has 96 vertices. Relative to the corresponding class of any saved seed, intersections of 96, 95 and 94 are excluded respectively by the fixed-class, one-replacement and present two-replacement covers. The minority intersection is therefore at most 93. The earlier majority-class cover gives an intersection of at most 95 with the other seed class. Their sum is at most 188.

The seed has 192 vertices and the proposed snake has 193. Consequently at least four seed vertices must be omitted and at least five new vertices introduced. The argument transports to cube-isometric copies by applying an inverse automorphism; parity classes may exchange. It depends on the stated native finite premises and does not assert sufficiency of those changes.

There is also an exact restricted maximum over snakes whose one complete 96-vertex parity class differs from a saved class by at most two replacements. Alternation gives at most 192 edges. That top case would make the selected class the minority class and is excluded. Thus the family maximum is 191, attained by an original seed in its zero-replacement part. This is no global upper bound.

## Paused frontier

The next construction must allow at least three replacements in the minority class relative to every saved seed. The smaller degree formulation is now an implemented way to choose those replacements and the opposite class jointly. On resumption, try a bounded three-replacement search, inspect any cycle components, and add only verified cycle cuts. A broader variant may maximize retained seed vertices while allowing more replacements, but it is unimplemented and unsearched. Partial greedy growth remains optional when useful.

The maintained interval remains 191<=a(9)<=233, with an independent full rebuild of the contributor's 233 theorem pending. The 196 conjecture remains unresolved. The user requested a pause after this round; publish the checkpoint and pause the goal.
