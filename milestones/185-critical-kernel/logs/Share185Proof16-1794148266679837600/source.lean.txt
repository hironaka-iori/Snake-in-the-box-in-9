import Share185Proof15
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem lit_posP_S {a : Nat} (h : posP M a = true) :
    litTrue (tauS S E M X Mr cs tots) (decodeLit a) = S (vl M a) := by
  have h' := h
  simp only [posP, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h'
  obtain ⟨⟨h0, h2⟩, hp⟩ := h'
  rw [decode_eq _ h2]
  simp [lv, h0, tauS_old (oldVar_of_isP hp), tau, vl, isP_get hp]


end Snake9.LocalWindow.Tags185
