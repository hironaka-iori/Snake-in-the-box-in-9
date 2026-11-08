import Share185Proof25
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem totOK_getD {w : List Nat} {cens : List Centre} (h : tots.all (totOK M X w cens) = true)
    (i : Nat) : totOK M X w cens (tots.getD i dfltTot) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hc : tots[i]? with
  | none => simp [totOK, dfltTot, capL, List.isPerm]
  | some t => exact List.all_eq_true.1 h t (List.mem_of_getElem? hc)


end Snake9.LocalWindow.Tags185
