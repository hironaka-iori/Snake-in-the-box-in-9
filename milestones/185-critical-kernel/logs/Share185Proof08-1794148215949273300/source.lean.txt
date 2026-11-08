import Share185Proof07
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem uOf_get {a q t : Nat} (h : uOf X a = some (q, t)) : X.get (a / 2) = .u q t := by
  unfold uOf at h; split at h <;> simp_all


end Snake9.LocalWindow.Tags185
