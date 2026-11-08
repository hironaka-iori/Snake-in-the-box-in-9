import Share185Proof19
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem lit_posU {a : Nat} (h : posU M X a = true) :
    litTrue (tauS S E M X Mr cs tots) (decodeLit a) =
      decide ((uQT X a).2 ≤ fl Mr S (uQT X a).1) := by
  have h' := h
  simp only [posU, Bool.and_eq_true] at h'
  obtain ⟨h0, h2, hn⟩ := posS_parts h'.1
  rw [decode_eq _ h2]
  simp only [lv, h0, if_true]
  rw [tauS_su hn (Or.inr h'.2), sval_u h'.2]


end Snake9.LocalWindow.Tags185
