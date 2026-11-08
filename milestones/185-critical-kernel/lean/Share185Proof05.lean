import Share185Proof04
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem tauS_old {x : Nat} (h : oldVar M x = true) :
    tauS S E M X Mr cs tots x = tau S E M cs x := by
  unfold tauS; rw [if_pos h]


end Snake9.LocalWindow.Tags185
