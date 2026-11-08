import Share185Proof05
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem baseS_old {x : Nat} (h : oldVar M x = true) :
    baseS S E M X Mr x = base S E M x := by
  unfold baseS; rw [if_pos h]


end Snake9.LocalWindow.Tags185
