import Share185Proof42
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem lit_neg {τ : Nat → Bool} {x : Nat} (hx : 2 ≤ x) :
    litTrue τ (decodeLit x) = !lv τ (negL x) := by
  rw [decode_eq _ hx, lv_negL _ hx, Bool.not_not]


end Snake9.LocalWindow.Tags185
