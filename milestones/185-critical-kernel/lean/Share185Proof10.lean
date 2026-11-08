import Share185Proof09
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem uOf_of_isU {a : Nat} (h : isU X a = true) : uOf X a = some (uQT X a) := by
  unfold isU at h; unfold uQT
  cases hs : uOf X a with
  | none => rw [hs] at h; simp at h
  | some r => simp


end Snake9.LocalWindow.Tags185
