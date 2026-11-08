import Share185Proof18
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem lit_posSq {a : Nat} (h : posSq M X a = true) :
    litTrue (tauS S E M X Mr cs tots) (decodeLit a) = emptyPred S (sqQ X a) (sqAB X a) := by
  have h' := h
  simp only [posSq, Bool.and_eq_true] at h'
  obtain ⟨h0, h2, hn⟩ := posS_parts h'.1
  rw [decode_eq _ h2]
  simp only [lv, h0, if_true]
  rw [tauS_su hn (Or.inl h'.2), sval_sq h'.2]


end Snake9.LocalWindow.Tags185
