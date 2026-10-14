# Square-face investigation

The manuscript now contains a complete written argument for the bound `a(9) <= 254`. The local singleton-square lemma is now proved in Lean for every path length and every selected vertex. The global square-incidence bijections remain to be checked. The end-to-end Lean-checked interval remains `191 <= a(9) <= 255`.

## Fully checked counterexample

`SquareCounterexample.lean` constructs a 137-edge snake under the existing `Snake9.Snake` definition, with initial vertex 145 and final vertex 288. The vertex at index 127 is zero. Among all coordinate squares through zero, exactly the square with coordinate pair (2,3) intersects the snake only at zero. Its four vertices are 0,4,8,12. Zero is 127 and 10 path edges from the endpoints, whose Hamming distances from zero are 3 and 2.

The module checks all 9,453 unordered path-vertex pairs, the complete square enumeration, its equivalence to the explicit singleton-square predicate, and the refutation of the universal assertion that every internal snake vertex has at least two singleton squares. Axiom audits use only the standard logical foundations; there are no proof placeholders or unchecked computation axioms.

This refutes a direct extension to all open paths of a local condition used in cycle upper bounds. It does not refute a statement restricted to longest paths.

## Written refinement and remaining proof obligations

The manuscript proves that every vertex of an induced path in Q9 has at least one singleton square. The argument classifies the selected neighbors of a translated vertex, forces pair vertices when no singleton square exists, and derives more than two endpoints. Counting all 4,608 square faces then gives, for a path on v >= 2 vertices,

`2*A0 + A1 + 35*v + 2 = 9216`.

Since A1 is the sum of the local singleton-square counts, the lemma gives A1 >= v. Therefore 36*v+2 <= 9216, yielding at most 255 vertices and 254 edges.

`SquareCountingLogic.lean` checks the arithmetic identity and the upper-bound deduction **conditional on** the incidence and singleton-count premises. It also checks the elementary endpoint-count contradictions. It does not yet derive these premises from `Snake9.Snake`. The local geometric theorem is now proved in `SingletonSquareLemma.lean`, supported by `PathStructure.lean` and `CubeLocal.lean`. It proves both existence of a singleton square under the same predicate used by the counterexample and positivity of its enumerated count. It includes short paths and XOR translation. The axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`. All 14 core modules build successfully; see `singleton-lean-build.log`. The global incidence bijections are the remaining Lean obligation for 254.

## Solver evidence

The local search fixes a selected internal vertex at zero with selected neighbors 1 and 2. An alpha value of zero forces every pair of unused coordinates into the selected set; an alpha value at most one permits only the pair (2,3) to be absent, using coordinate symmetry. The model enforces one connected induced path, with variable length and free endpoints.

- Alpha at most one: feasible 123-edge witness.
- Alpha at most one and both endpoints at Hamming distance at least two from zero: feasible 137-edge witness, checked in Lean as above.
- Alpha zero: INFEASIBLE, about 0.31 seconds; no proof certificate imported into Lean.
- Alpha at most one and both endpoints at Hamming distance at least three: INFEASIBLE, about 0.91 seconds; uncertified.
- A relaxation allowing disconnected components while excluding four-cycles, with exactly two degree-one vertices: alpha zero INFEASIBLE, about 0.22 seconds; uncertified.

An independent square census of the 131 published 191-edge examples found minimum local alpha values of 3 in 67 examples, 4 in 47 examples, and 5 in 17 examples. This describes that bank only. Every example satisfied the square-count identity in an independent Python audit. These bank calculations are not Lean-certified.

Source for the cycle method: A. Lukito and A. J. van Zanten, Journal of Combinatorial Mathematics and Combinatorial Computing 39 (2001), 147-156, especially pages 150-151: https://combinatorialpress.com/article/jcmcc/Volume%20039/vol-039-paper%2012.pdf
