import Share185Proof12
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem tauS_su {a : Nat} (hn : oldVar M (a / 2) = false) (h : isSq X a = true ∨ isU X a = true) :
    tauS S E M X Mr cs tots (a / 2) = sval S Mr X (a / 2) := by
  unfold tauS; rw [if_neg (by simp [hn])]
  rcases h with h | h
  · rw [sqOf_get (sqOf_of_isSq h)]
  · rw [uOf_get (uOf_of_isU h)]



end Snake9.LocalWindow.Tags185
