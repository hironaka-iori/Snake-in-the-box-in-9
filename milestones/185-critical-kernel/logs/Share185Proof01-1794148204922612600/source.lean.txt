import Share185Proof00
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem lv_negL (τ : Nat → Bool) {x : Nat} (hx : 2 ≤ x) : lv τ (negL x) = !lv τ x := by
  unfold negL lv
  by_cases h : x % 2 = 0
  · have h1 : (x + 1) % 2 = 1 := by omega
    have h2 : (x + 1) / 2 = x / 2 := by omega
    simp [h, h1, h2]
  · have h1 : (x - 1) % 2 = 0 := by omega
    have h2 : (x - 1) / 2 = x / 2 := by omega
    simp [h, h1, h2]


end Snake9.LocalWindow.Tags185
