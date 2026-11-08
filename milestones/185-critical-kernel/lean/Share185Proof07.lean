import Share185Proof06
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sqOf_get {a q x y : Nat} (h : sqOf X a = some (q, x, y)) : X.get (a / 2) = .sq q x y := by
  unfold sqOf at h; split at h <;> simp_all


end Snake9.LocalWindow.Tags185
