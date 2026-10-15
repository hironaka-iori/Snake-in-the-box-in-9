# Square-face investigation

The manuscript's bound `a(9) <= 254` is now checked end to end in Lean. The verified interval is `191 <= a(9) <= 254`. The new proof uses four-corner summation, replacing the previously pending canonical-square census argument.

## Fully checked counterexample

`SquareCounterexample.lean` constructs a 137-edge snake under the existing `Snake9.Snake` definition, with initial vertex 145 and final vertex 288. The vertex at index 127 is zero. Among all coordinate squares through zero, exactly the square with coordinate pair (2,3) intersects the snake only at zero. Its four vertices are 0,4,8,12. Zero is 127 and 10 path edges from the endpoints, whose Hamming distances from zero are 3 and 2.

The module checks all 9,453 unordered path-vertex pairs, the complete square enumeration, its equivalence to the explicit singleton-square predicate, and the refutation of the universal assertion that every internal snake vertex has at least two singleton squares. Axiom audits use only the standard logical foundations; there are no proof placeholders or unchecked computation axioms.

This refutes a direct extension to all open paths of a local condition used in cycle upper bounds. It does not refute a statement restricted to longest paths.

## Fully checked incidence refinement

`work/spectral/SquareIncidence.lean` imports the general singleton-square theorem from the standard-library core and uses pinned mathlib for finite sums. Let E count empty squares from their corners, T count singleton incidences at selected vertices, and W count selected centers with two selected coordinate neighbors. The module derives

`2*E + 4*T + 144*v = 36864 + 4*W`.

The proof verifies that coordinate flips are involutive permutations, excludes fully selected squares, checks the local four-corner identity, sums it over all 36 coordinate pairs and 512 cube vertices, and proves that the selected-vertex indicator sums to v.

The singleton-square lemma gives T >= v. A selected two-edge corner determines an internal path vertex, and at most one coordinate pair contributes at each center. This gives W <= v-2 for v >= 2. The resulting bound is at most 255 vertices and 254 edges. The final theorem uses `Snake9.Snake` and supplies the paired lower and upper bounds.

Axiom audits list only `propext`, `Classical.choice`, and `Quot.sound`. There are no proof placeholders, added mathematical axioms, unchecked native computations, or assumed census premises. The portable reproduction driver is `work/spectral/verify_incidence.py`; `--fresh-core` rebuilds all 14 core modules from source in a new directory. Its output is recorded in `outputs/incidence-reproduction.log`.

The original unoriented census identity `2*A0 + A1 + 35*v + 2 = 9216` remains a written mathematical observation. `SquareCountingLogic.lean` checks its arithmetic conditionally; its exact census bijections are not separately certified. The upper bound 254 no longer depends on completing those bijections. The paper now follows the checked four-corner proof.

## Solver evidence

The local search fixes a selected internal vertex at zero with selected neighbors 1 and 2. An alpha value of zero forces every pair of unused coordinates into the selected set; an alpha value at most one permits only the pair (2,3) to be absent, using coordinate symmetry. The model enforces one connected induced path, with variable length and free endpoints.

- Alpha at most one: feasible 123-edge witness.
- Alpha at most one and both endpoints at Hamming distance at least two from zero: feasible 137-edge witness, checked in Lean as above.
- Alpha zero: INFEASIBLE, about 0.31 seconds; no proof certificate imported into Lean.
- Alpha at most one and both endpoints at Hamming distance at least three: INFEASIBLE, about 0.91 seconds; uncertified.
- A relaxation allowing disconnected components while excluding four-cycles, with exactly two degree-one vertices: alpha zero INFEASIBLE, about 0.22 seconds; uncertified.

An independent square census of the 131 published 191-edge examples found minimum local alpha values of 3 in 67 examples, 4 in 47 examples, and 5 in 17 examples. This describes that bank only. Every example satisfied the square-count identity in an independent Python audit. These bank calculations are not Lean-certified.

Source for the cycle method: A. Lukito and A. J. van Zanten, Journal of Combinatorial Mathematics and Combinatorial Computing 39 (2001), 147-156, especially pages 150-151: https://combinatorialpress.com/article/jcmcc/Volume%20039/vol-039-paper%2012.pdf
