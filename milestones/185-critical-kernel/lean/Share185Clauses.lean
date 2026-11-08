import Share185Counters
namespace Snake9.LocalWindow.Tags185
open Snake9.LocalWindow.Tags
open Snake9.LocalWindow
variable {S E : Nat → Bool} {M : MT} {X : MS} {Mr : Nat} {cs : List Ctr} {tots : List Tot}
variable {w : List Nat} {cens : List Centre}
theorem kind_emp {k : TotKind} {q : Nat} (h : isEmp q k = true) : k = .emp q := by
  cases k <;> simp_all [isEmp]

theorem kind_nb {k : TotKind} {q : Nat} (h : isNb q k = true) : k = .nb q := by
  cases k <;> simp_all [isNb]

/-- The arithmetic of a threshold clause: `u` false, `ge` true and `gd` false clash. -/
theorem share_arith {Mr e0 d t cn dd : Nat} (hd : 1 ≤ d) (hdd : d ≤ dd) (he : cn ≤ e0)
    (hm : t * dd ≤ Mr * cn) (hu : ¬ t ≤ Mr * e0 / d) : False := by
  apply hu
  rw [Nat.le_div_iff_mul_le (by omega)]
  exact Nat.le_trans (Nat.mul_le_mul_left t hdd)
    (Nat.le_trans hm (Nat.mul_le_mul_left Mr he))

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

theorem sound_shareCap {i cap : Nat} {cl : List Nat} (h : ckShareCap M X tots cap i cl = true)
    (ht : tots.all (totOK M X w cens) = true) (hs : shareSum Mr S cens ≤ cap) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  match cl, h with
  | [x], h =>
    simp only [ckShareCap, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hx, hk⟩, h⟩ := h
    split at h
    · rename_i lo hi c ho
      simp only [decide_eq_true_eq] at h
      apply clause_intro; intro hf
      have fx := hf x (by simp)
      rw [lit_neg hx, Bool.not_eq_false', tInfo_sem ho, decide_eq_true_eq] at fx
      have h1 := bc_total (S := S) (E := E) (M := M) (X := X) (Mr := Mr) (tots := tots) i lo hi
      have h2 := cap_total (S := S) (E := E) (Mr := Mr) (totOK_getD ht i) hk
      omega
    · simp at h

theorem sound_clauseS {cap : Nat} {t : TagS} {cl : List Nat}
    (h : ckClauseS M X Mr cs tots w cap t cl = true)
    (hcs : cs.all (ctrOK M cens) = true) (ht : tots.all (totOK M X w cens) = true)
    (ax : AxiomsS S E w cens Mr cap) :
    clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true := by
  cases t with
  | old t =>
    simp only [ckClauseS, Bool.and_eq_true] at h
    exact old_clause h.1 (sound_clause h.2 hcs ax.toAxioms)
  | emptyE => exact sound_emptyE h
  | totUp i => exact sound_totUp h ht
  | totDown i => exact sound_totDown h ht
  | shareCl eT dT => exact sound_shareCl h ht ax.window_sel
  | shareCap i => exact sound_shareCap h ht ax.share_le

theorem sound_allS {cap : Nat} : ∀ {tags : List TagS} {raw : List (List Nat)},
    ckAllS M X Mr cs tots w cap tags raw = true →
    cs.all (ctrOK M cens) = true → tots.all (totOK M X w cens) = true →
    AxiomsS S E w cens Mr cap →
    ∀ cl ∈ raw, clauseTrue (tauS S E M X Mr cs tots) (cl.map decodeLit) = true
  | [], [], _, _, _, _ => by simp
  | t :: ts, cl :: cls, h, hcs, ht, ax => by
    simp only [ckAllS, Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact sound_clauseS h.1 hcs ht ax
    · exact sound_allS h.2 hcs ht ax x hx
  | [], _ :: _, h, _, _, _ => by simp [ckAllS] at h
  | _ :: _, [], h, _, _, _ => by simp [ckAllS] at h



end Snake9.LocalWindow.Tags185
