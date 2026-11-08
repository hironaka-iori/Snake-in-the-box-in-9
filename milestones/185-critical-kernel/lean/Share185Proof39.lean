import Share185Proof38
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem cap_total {w : List Nat} {cens : List Centre} {t : Tot}
    (h : totOK M X w cens t = true) (hk : isCap t.kind = true) :
    t.lits.countP (lv (baseS S E M X Mr)) ≤ shareSum Mr S cens := by
  unfold totOK at h
  cases hk' : t.kind with
  | emp q => rw [hk'] at hk; simp [isCap] at hk
  | nb q => rw [hk'] at hk; simp [isCap] at hk
  | cap spec =>
    rw [hk'] at h
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨_, hu, hm, hs⟩ := h
    have : t.lits.countP (lv (baseS S E M X Mr)) =
        (t.lits.map (uQT X)).countP (fun p => decide (p.2 ≤ fl Mr S p.1)) := by
      rw [List.countP_map]
      apply List.countP_congr
      intro a ha
      rw [base_posU (hu a ha)]; rfl
    have heq : (instBEqProd : BEq (Nat × Nat)) = instBEqOfDecidableEq := by
      apply congrArg BEq.mk
      funext a b
      exact Bool.beq_eq_decide_eq a b
    rw [heq] at hm
    rw [this, (List.isPerm_iff.mp hm).countP_eq]
    exact capL_le cens spec hs


end Snake9.LocalWindow.Tags185
