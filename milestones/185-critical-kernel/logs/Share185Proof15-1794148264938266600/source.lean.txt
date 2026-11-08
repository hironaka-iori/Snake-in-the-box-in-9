import Share185Proof14
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem posS_parts {a : Nat} (h : posS M a = true) :
    a % 2 = 0 ∧ 2 ≤ a ∧ oldVar M (a / 2) = false := by
  simp only [posS, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩


end Snake9.LocalWindow.Tags185
