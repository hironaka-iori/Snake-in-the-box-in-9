import Share185Proof43
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sound_totUp {i : Nat} {cl : List Nat} (h : ckTotUp M X tots i cl = true)
    (ht : tots.all (totOK M X w cens) = true) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  match cl, h with
  | [o, x], h =>
    simp only [ckTotUp, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hx, h⟩ := h
    split at h
    · rename_i lo hi c ho
      have ho2 : 2 ≤ o := by
        unfold tInfo at ho; split at ho
        · exact (posS_parts (by assumption)).2.1
        · simp at ho
      apply clause_intro; intro hf
      have fo := hf o (by simp); have fx := hf x (by simp)
      rw [decode_eq _ ho2, tInfo_sem ho, decide_eq_false_iff_not] at fo
      rw [lit_neg hx, Bool.not_eq_false'] at fx
      have key : ∀ pos, subUp lo hi c (litInfo M X tots i (negL x) pos) = true → False := by
        intro pos hs
        unfold subUp at hs
        split at hs
        · rename_i l hh c1 hl
          simp only [decide_eq_true_eq] at hs
          rw [litInfo_sem ht hl, decide_eq_true_eq] at fx
          have s1 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
            (lo := lo) (mid := l) (hi := hi) hs.1 (by omega)
          have s2 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
            (lo := l) (mid := hh) (hi := hi) hs.2.1 hs.2.2.1
          unfold bc at fo fx
          omega
        · simp at hs
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · exact key _ h
      · exact key _ h
    · simp at h
  | [o, x, y], h =>
    simp only [ckTotUp, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hx, hy⟩, h⟩ := h
    split at h
    · rename_i lo hi c ho
      have ho2 : 2 ≤ o := by
        unfold tInfo at ho; split at ho
        · exact (posS_parts (by assumption)).2.1
        · simp at ho
      apply clause_intro; intro hf
      have fo := hf o (by simp); have fx := hf x (by simp); have fy := hf y (by simp)
      rw [decode_eq _ ho2, tInfo_sem ho, decide_eq_false_iff_not] at fo
      rw [lit_neg hx, Bool.not_eq_false'] at fx
      rw [lit_neg hy, Bool.not_eq_false'] at fy
      unfold twoUp at h
      split at h
      · rename_i l1 h1 c1 l2 h2 c2 hl1 hl2
        simp only [decide_eq_true_eq] at h
        rw [litInfo_sem ht hl1, decide_eq_true_eq] at fx
        rw [litInfo_sem ht hl2, decide_eq_true_eq] at fy
        have s1 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := lo) (mid := l1) (hi := hi) h.1 (by omega)
        have s2 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := l1) (mid := h1) (hi := hi) h.2.1 (by omega)
        have s3 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := h1) (mid := l2) (hi := hi) h.2.2.1 (by omega)
        have s4 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := l2) (mid := h2) (hi := hi) h.2.2.2.1 h.2.2.2.2.1
        unfold bc at fo fx fy
        omega
      · simp at h
    · simp at h


end Snake9.LocalWindow.Tags185
