import Share185Proof16
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem base_posSq {a : Nat} (h : posSq M X a = true) :
    lv (baseS S E M X Mr) a = emptyPred S (sqQ X a) (sqAB X a) := by
  simp only [posSq, Bool.and_eq_true] at h
  obtain ⟨h0, h2, hn⟩ := posS_parts h.1
  simp only [lv, h0, if_true]
  unfold baseS; rw [if_neg (by simp [hn]), sval_sq h.2]


end Snake9.LocalWindow.Tags185
