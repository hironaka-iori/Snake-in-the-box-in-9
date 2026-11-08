import Share185Proof01
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem negL_ge {x : Nat} (hx : 2 ≤ x) : 2 ≤ negL x := by
  unfold negL; split <;> omega


end Snake9.LocalWindow.Tags185
