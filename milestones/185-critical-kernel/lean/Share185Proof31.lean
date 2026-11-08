import Share185Proof30
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem nb_total {w : List Nat} {cens : List Centre} {t : Tot} {q : Nat}
    (h : totOK M X w cens t = true) (hk : t.kind = .nb q) :
    t.lits.countP (lv (baseS S E M X Mr)) = cnt S (nbrs q) ∧ t.lits.length = 9 := by
  unfold totOK at h
  rw [hk] at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨_, hp, hm, _⟩ := h
  constructor
  · unfold cnt
    rw [← List.countP_eq_length_filter, ← hm, List.countP_map]
    apply List.countP_congr
    intro a ha
    have hP : isP M (a / 2) = true := by
      have := hp a ha
      simp only [posP, Bool.and_eq_true] at this; exact this.2
    have hb : lv (baseS S E M X Mr) a = S (vl M a) := by
      rw [lv_congr (τ₂ := base S E M) (baseS_old (oldVar_of_isP hP))]
      exact base_posP (hp a ha)
    simp [hb]
  · have := congrArg List.length hm
    rw [List.length_map] at this
    rw [this]; rfl


end Snake9.LocalWindow.Tags185
