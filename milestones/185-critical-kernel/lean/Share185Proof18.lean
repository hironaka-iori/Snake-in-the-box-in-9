import Share185Proof17
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem base_posU {a : Nat} (h : posU M X a = true) :
    lv (baseS S E M X Mr) a = decide ((uQT X a).2 ≤ fl Mr S (uQT X a).1) := by
  simp only [posU, Bool.and_eq_true] at h
  obtain ⟨h0, h2, hn⟩ := posS_parts h.1
  simp only [lv, h0, if_true]
  unfold baseS; rw [if_neg (by simp [hn]), sval_u h.2]


end Snake9.LocalWindow.Tags185
