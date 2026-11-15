import Std

set_option Elab.async false

namespace CyclePotential219

private theorem sum_append_int (xs ys : List Int) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons a tail ih =>
      simp only [List.cons_append, List.sum_cons, ih]
      omega

private theorem range_sum_succ (f : Nat → Int) (n : Nat) :
    ((List.range (n + 1)).map f).sum = ((List.range n).map f).sum + f n := by
  rw [List.range_succ, List.map_append, sum_append_int]
  simp

/-- Consecutive potential differences telescope along the indexed path.
No assumption about the sign of the weights is needed for this deduction. -/
theorem path_potential_bound (potential weight : Nat → Int) (n : Nat)
    (steps : ∀ i, i < n → potential (i + 1) - potential i ≤ weight i) :
    potential n - potential 0 ≤ ((List.range n).map weight).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      have previous := ih (by
        intro i hi
        exact steps i (by omega))
      have last := steps n (by omega)
      rw [range_sum_succ]
      omega

/-- A lower bound involving the omitted closing edge and its endpoint
potentials yields a lower bound on the entire cycle weight. -/
theorem closing_edge_bound (potential weight : Nat → Int) (n : Nat)
    (D closing : Int)
    (steps : ∀ i, i < n → potential (i + 1) - potential i ≤ weight i)
    (boundary : 2 * D ≤ potential n - potential 0 + closing) :
    2 * D ≤ ((List.range n).map weight).sum + closing := by
  have path := path_potential_bound potential weight n steps
  omega

private theorem path_cost_identity (selected : Nat → Int) (D : Int) (n : Nat) :
    ((List.range n).map (fun i => 2 * D - selected i - selected (i + 1))).sum =
      (n : Int) * (2 * D) - 2 * ((List.range n).map selected).sum +
      selected 0 - selected n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [range_sum_succ, range_sum_succ, ih]
      simp only [Int.natCast_succ, Int.add_mul, Int.one_mul]
      omega

/-- For edge cost 2D-X(u)-X(v), a cycle's weight counts each vertex twice. -/
theorem cycle_cost_identity (selected : Nat → Int) (D : Int) (n : Nat) :
    ((List.range n).map (fun i => 2 * D - selected i - selected (i + 1))).sum +
      (2 * D - selected n - selected 0) =
      ((n : Int) + 1) * (2 * D) -
      2 * ((List.range (n + 1)).map selected).sum := by
  rw [path_cost_identity, range_sum_succ]
  simp only [Int.add_mul, Int.one_mul]
  omega

/-- Integer-scaled edge-deleted potentials certify the cycle occupancy
inequality. For a simple cycle, the indexed sum counts each vertex once. -/
theorem cycle_occupancy_bound (potential selected : Nat → Int) (D : Int) (n : Nat)
    (steps : ∀ i, i < n → potential (i + 1) - potential i ≤
      2 * D - selected i - selected (i + 1))
    (boundary : 2 * D ≤ potential n - potential 0 +
      (2 * D - selected n - selected 0)) :
    ((List.range (n + 1)).map selected).sum ≤ (n : Int) * D := by
  have lower := closing_edge_bound potential
    (fun i => 2 * D - selected i - selected (i + 1)) n D
    (2 * D - selected n - selected 0) steps boundary
  rw [cycle_cost_identity] at lower
  have rearrange : (n : Int) * (2 * D) = 2 * ((n : Int) * D) := by
    rw [← Int.mul_assoc, Int.mul_comm (n : Int) 2, Int.mul_assoc]
  simp only [Int.add_mul, Int.one_mul] at lower
  rw [rearrange] at lower
  omega

#print axioms path_potential_bound
#print axioms closing_edge_bound
#print axioms cycle_cost_identity
#print axioms cycle_occupancy_bound
end CyclePotential219
