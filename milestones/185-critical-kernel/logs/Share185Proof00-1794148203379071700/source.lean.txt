import Share185Definitions
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem lv_congr {τ₁ τ₂ : Nat → Bool} {a : Nat} (h : τ₁ (a / 2) = τ₂ (a / 2)) :
    lv τ₁ a = lv τ₂ a := by
  unfold lv; rw [h]


end Snake9.LocalWindow.Tags185
