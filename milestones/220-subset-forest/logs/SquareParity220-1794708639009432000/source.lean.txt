import Std

set_option Elab.async false

namespace SquareParity220

/-- The induced-edge product makes the linear expression equal to endpoint
disagreement for Boolean vertex choices. -/
theorem boolean_disagreement (a b : Bool) :
    (if a then (1 : Int) else 0) + (if b then (1 : Int) else 0) -
      2 * ((if a then (1 : Int) else 0) * (if b then (1 : Int) else 0)) =
      (if a = b then (0 : Int) else 1) := by
  cases a <;> cases b <;> decide

/-- One edge disagreement cannot exceed the other three on a square.
The four rotations give all odd subsets containing one edge. -/
theorem square_single_edge (a b c d : Bool) :
    (if a = b then (0 : Int) else 1) -
      (if b = c then (0 : Int) else 1) -
      (if c = d then (0 : Int) else 1) -
      (if d = a then (0 : Int) else 1) ≤ 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Three square-edge disagreements, less the fourth, have total at most
two. Rotations give every odd subset containing three edges. -/
theorem square_three_edges (a b c d : Bool) :
    (if a = b then (0 : Int) else 1) +
      (if b = c then (0 : Int) else 1) +
      (if c = d then (0 : Int) else 1) -
      (if d = a then (0 : Int) else 1) ≤ 2 := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

end SquareParity220

#print axioms SquareParity220.boolean_disagreement
#print axioms SquareParity220.square_single_edge
#print axioms SquareParity220.square_three_edges
