import Share185Proof10
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sval_sq {a : Nat} (h : isSq X a = true) :
    sval S Mr X (a / 2) = emptyPred S (sqQ X a) (sqAB X a) := by
  have := sqOf_get (sqOf_of_isSq h)
  unfold sval; rw [this]; rfl


end Snake9.LocalWindow.Tags185
