import Share185Proof48
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem sound_shareCl {eT dT : Nat} {cl : List Nat} (h : ckShareCl M X Mr tots eT dT cl = true)
    (ht : tots.all (totOK M X w cens) = true) (hw : ∀ v ∈ w, S v = true) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  match cl, h with
  | [u, x], h =>
    simp only [ckShareCl, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hx, hu⟩, he⟩, hn⟩, h⟩ := h
    split at h
    · rename_i l hh cn hl
      simp only [decide_eq_true_eq] at h
      apply clause_intro; intro hf
      have fu := hf u (by simp); have fx := hf x (by simp)
      rw [lit_posU hu, decide_eq_false_iff_not] at fu
      rw [lit_neg hx, Bool.not_eq_false', litInfo_sem ht hl, decide_eq_true_eq] at fx
      have hE := emp_total (S := S) (E := E) (Mr := Mr) (totOK_getD ht eT) (kind_emp he)
      have hN := nb_total (S := S) (E := E) (Mr := Mr) (totOK_getD ht dT) (kind_nb hn)
      have hP := nb_pos (totOK_getD ht dT) (kind_nb hn) hw
      have hB := bc_total (S := S) (E := E) (M := M) (X := X) (Mr := Mr) (tots := tots) eT l hh
      have h9 : cnt S (nbrs (uQT X u).1) ≤ 9 := by
        have := hN.2; rw [← hN.1]
        exact Nat.le_trans List.countP_le_length (by omega)
      exact share_arith hP h9 (by omega) h fu
    · simp at h
  | [u, x, y], h =>
    simp only [ckShareCl, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hx, hy⟩, hu⟩, he⟩, hn⟩, h⟩ := h
    split at h
    · rename_i l hh cn l2 h2 c2 hl hl2
      simp only [decide_eq_true_eq] at h
      obtain ⟨rfl, h9, hm⟩ := h
      apply clause_intro; intro hf
      have fu := hf u (by simp); have fx := hf x (by simp); have fy := hf y (by simp)
      rw [lit_posU hu, decide_eq_false_iff_not] at fu
      rw [lit_neg hx, Bool.not_eq_false', litInfo_sem ht hl, decide_eq_true_eq] at fx
      rw [decode_eq _ hy, litInfo_sem ht hl2, decide_eq_false_iff_not] at fy
      have hE := emp_total (S := S) (E := E) (Mr := Mr) (totOK_getD ht eT) (kind_emp he)
      have hN := nb_total (S := S) (E := E) (Mr := Mr) (totOK_getD ht dT) (kind_nb hn)
      have hP := nb_pos (totOK_getD ht dT) (kind_nb hn) hw
      have hB := bc_total (S := S) (E := E) (M := M) (X := X) (Mr := Mr) (tots := tots) eT l hh
      have hall : bc S E M X Mr tots dT 0 h2 = cnt S (nbrs (uQT X u).1) := by
        unfold bc blk
        rw [List.drop_zero, Nat.sub_zero, List.take_of_length_le (by omega)]
        exact hN.1
      rw [hall] at fy
      exact share_arith hP (Nat.le_sub_one_of_lt (by omega)) (by omega) hm fu
    · simp at h


end Snake9.LocalWindow.Tags185
