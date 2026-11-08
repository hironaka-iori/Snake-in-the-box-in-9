import Share185Proof44
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sound_totDown {i : Nat} {cl : List Nat} (h : ckTotDown M X tots i cl = true)
    (ht : tots.all (totOK M X w cens) = true) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  match cl, h with
  | [o, x], h =>
    simp only [ckTotDown, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ho2, hx⟩, h⟩ := h
    split at h
    · rename_i lo hi c ho
      apply clause_intro; intro hf
      have fo := hf o (by simp); have fx := hf x (by simp)
      rw [lit_neg ho2, tInfo_sem ho, Bool.not_eq_false', decide_eq_true_eq] at fo
      rw [decode_eq _ hx] at fx
      have key : ∀ pos, subDown lo hi c (litInfo M X tots i x pos) = true → False := by
        intro pos hs
        unfold subDown at hs
        split at hs
        · rename_i l hh c1 hl
          simp only [decide_eq_true_eq] at hs
          rw [litInfo_sem ht hl, decide_eq_false_iff_not] at fx
          have s1 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
            (lo := lo) (mid := l) (hi := hi) hs.1 (by omega)
          have s2 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
            (lo := l) (mid := hh) (hi := hi) hs.2.1 hs.2.2.1
          have b1 := countP_blk_le (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits lo l
          have b2 := countP_blk_le (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits hh hi
          unfold bc at fo fx
          omega
        · simp at hs
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · exact key _ h
      · exact key _ h
    · simp at h
  | [o, x, y], h =>
    simp only [ckTotDown, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨ho2, hx⟩, hy⟩, h⟩ := h
    split at h
    · rename_i lo hi c ho
      apply clause_intro; intro hf
      have fo := hf o (by simp); have fx := hf x (by simp); have fy := hf y (by simp)
      rw [lit_neg ho2, tInfo_sem ho, Bool.not_eq_false', decide_eq_true_eq] at fo
      rw [decode_eq _ hx] at fx
      rw [decode_eq _ hy] at fy
      unfold twoDown at h
      split at h
      · rename_i l1 h1 c1 l2 h2 c2 hl1 hl2
        simp only [decide_eq_true_eq] at h
        rw [litInfo_sem ht hl1, decide_eq_false_iff_not] at fx
        rw [litInfo_sem ht hl2, decide_eq_false_iff_not] at fy
        have s1 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := lo) (mid := l1) (hi := hi) h.1 (by omega)
        have s2 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := l1) (mid := h1) (hi := hi) h.2.1 (by omega)
        have s3 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := h1) (mid := l2) (hi := hi) h.2.2.1 (by omega)
        have s4 := countP_blk_split (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits
          (lo := l2) (mid := h2) (hi := hi) h.2.2.2.1 h.2.2.2.2.1
        have b1 := countP_blk_le (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits lo l1
        have b2 := countP_blk_le (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits h1 l2
        have b3 := countP_blk_le (lv (baseS S E M X Mr)) (tots.getD i dfltTot).lits h2 hi
        unfold bc at fo fx fy
        omega
      · simp at h
    · simp at h


end Snake9.LocalWindow.Tags185
