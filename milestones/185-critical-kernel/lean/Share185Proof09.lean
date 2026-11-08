import Share185Proof08
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sqOf_of_isSq {a : Nat} (h : isSq X a = true) :
    sqOf X a = some (sqQ X a, sqAB X a) := by
  unfold isSq at h; unfold sqQ sqAB
  cases hs : sqOf X a with
  | none => rw [hs] at h; simp at h
  | some r => simp


end Snake9.LocalWindow.Tags185
