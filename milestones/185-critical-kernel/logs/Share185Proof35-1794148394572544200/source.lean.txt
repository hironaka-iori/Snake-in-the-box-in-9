import Share185Proof34
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem countP_range_le (x : Nat) : ∀ n, (List.range n).countP (fun t => decide (t + 1 ≤ x)) ≤ x
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.countP_append]
    have ih := countP_range_le x n
    have hl : (List.range n).countP (fun t => decide (t + 1 ≤ x)) ≤ n := by
      have := List.countP_le_length (p := fun t => decide (t + 1 ≤ x)) (l := List.range n)
      rwa [List.length_range] at this
    by_cases hx : n + 1 ≤ x
    · simp [hx]; omega
    · simp [hx]; omega


end Snake9.LocalWindow.Tags185
