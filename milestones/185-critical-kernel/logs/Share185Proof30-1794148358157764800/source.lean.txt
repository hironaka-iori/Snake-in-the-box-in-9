import Share185Proof29
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem emp_total {w : List Nat} {cens : List Centre} {t : Tot} {q : Nat}
    (h : totOK M X w cens t = true) (hk : t.kind = .emp q) :
    t.lits.countP (lv (baseS S E M X Mr)) ≤ emptyCount S q := by
  unfold totOK at h
  rw [hk] at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨_, hs, hsub⟩ := h
  have : t.lits.countP (lv (baseS S E M X Mr)) = (t.lits.map (sqAB X)).countP (emptyPred S q) := by
    rw [List.countP_map]
    apply List.countP_congr
    intro a ha
    obtain ⟨h1, h2⟩ := hs a ha
    rw [base_posSq h1, h2]; rfl
  rw [this]
  unfold emptyCount
  rw [← List.countP_eq_length_filter]
  exact (sublG_sublist hsub).countP_le


end Snake9.LocalWindow.Tags185
