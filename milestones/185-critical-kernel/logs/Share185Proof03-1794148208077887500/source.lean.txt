import Share185Proof02
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem oldVar_of_isP {x : Nat} (h : isP M x = true) : oldVar M x = true := by
  simp [oldVar, isP_get h]


end Snake9.LocalWindow.Tags185
