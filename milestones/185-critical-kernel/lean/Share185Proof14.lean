import Share185Proof13
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem lv_base_ok {l : Nat} (h : baseOKS M X l = true) :
    lv (tauS S E M X Mr cs tots) l = lv (baseS S E M X Mr) l := by
  simp only [baseOKS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, h⟩ := h
  apply lv_congr
  by_cases ho : oldVar M (l / 2) = true
  · rw [if_pos ho, Bool.or_eq_true] at h
    rw [tauS_old ho, baseS_old ho]
    rcases h with hp | hp
    · simp [tau, base, isP_get hp]
    · simp [tau, base, isE_get hp]
  · rw [if_neg ho, Bool.or_eq_true] at h
    have hn : oldVar M (l / 2) = false := by simpa using ho
    rw [tauS_su hn h]
    unfold baseS; rw [if_neg ho]


end Snake9.LocalWindow.Tags185
