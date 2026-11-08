import Share185Proof11
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sval_u {a : Nat} (h : isU X a = true) :
    sval S Mr X (a / 2) = decide ((uQT X a).2 ≤ fl Mr S (uQT X a).1) := by
  have := uOf_get (uOf_of_isU h)
  unfold sval; rw [this]; rfl


end Snake9.LocalWindow.Tags185
