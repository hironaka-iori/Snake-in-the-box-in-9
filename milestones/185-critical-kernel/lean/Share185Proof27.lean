import Share185Proof26
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem totOK_lits {w : List Nat} {cens : List Centre} {t : Tot} (h : totOK M X w cens t = true) :
    ∀ l ∈ t.lits, baseOKS M X l = true := by
  unfold totOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  exact h.1


end Snake9.LocalWindow.Tags185
