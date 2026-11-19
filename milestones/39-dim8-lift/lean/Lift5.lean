import Lift4
/-! Part 5: endpoint count and cardinality of the half; the reduction theorem. -/
set_option linter.deprecated false
namespace Dim8Lift
open Snake9

variable {M : Nat} {q : Snake M} {i : Nat} {b : Bool} {j1 : Nat}

def Ab (q : Snake M) (i : Nat) (b : Bool) (j1 t : Nat) : Bool := decide (1 ≤ t) && inP q i b j1 (t - 1)
def Bb (q : Snake M) (i : Nat) (b : Bool) (j1 t : Nat) : Bool := inP q i b j1 (t + 1)

theorem prev_nb (hi : i < 9) (hj : j1 ≤ M) {t : Nat} (ht : t ≤ j1) (hy : yy q i b t = true)
    (h : Ab q i b j1 t = true) : ∃ a, a < 8 ∧ SS q i b j1 (nb (proj i (V q t)) a) = true ∧
      proj i (V q (t - 1)) = nb (proj i (V q t)) a := by
  unfold Ab at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, hym⟩ := inP_yy h.2
  have e1 : t - 1 + 1 = t := by omega
  obtain ⟨a, ha, e⟩ := KA_from' (q := q) (i := i) (b := b) (j1 := j1) (t := t - 1) hi hj (by omega) hym
    (by rw [e1]; exact hy)
  rw [e1] at e
  exact ⟨a, ha, by unfold nb; rw [← e]; exact (SS_iff q i b j1 _).mpr ⟨t - 1, by omega, hym, rfl⟩, e⟩

theorem next_nb (hi : i < 9) (hj : j1 ≤ M) {t : Nat} (ht : t ≤ j1) (hy : yy q i b t = true)
    (h : Bb q i b j1 t = true) : ∃ a, a < 8 ∧ SS q i b j1 (nb (proj i (V q t)) a) = true ∧
      proj i (V q (t + 1)) = nb (proj i (V q t)) a := by
  unfold Bb at h
  obtain ⟨htj, hyp⟩ := inP_yy h
  obtain ⟨a, ha, e⟩ := KA_from (q := q) (i := i) (b := b) (j1 := j1) (t := t) hi hj htj hy hyp
  exact ⟨a, ha, by unfold nb; rw [← e]; exact (SS_iff q i b j1 _).mpr ⟨t + 1, htj, hyp, rfl⟩, e⟩

theorem any_char (hi : i < 9) (hj : j1 ≤ M) {t : Nat} (ht : t ≤ j1) (hy : yy q i b t = true) :
    anyB (SS q i b j1) (proj i (V q t)) = (Ab q i b j1 t || Bb q i b j1 t) := by
  apply Bool.eq_iff_iff.mpr
  rw [anyB_iff]; simp only [Bool.or_eq_true]
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨t', ht', hy', _, s⟩ := NBR hi hj ht hy ha h
    rcases s with s | s
    · right; unfold Bb; rw [← s]; exact inP_of ht' hy'
    · left; unfold Ab; simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by omega, ?_⟩; have : t - 1 = t' := by omega
      rw [this]; exact inP_of ht' hy'
  · rintro (h | h)
    · obtain ⟨a, ha, h1, _⟩ := prev_nb hi hj ht hy h; exact ⟨a, ha, h1⟩
    · obtain ⟨a, ha, h1, _⟩ := next_nb hi hj ht hy h; exact ⟨a, ha, h1⟩

theorem two_char (hi : i < 9) (hj : j1 ≤ M) {t : Nat} (ht : t ≤ j1) (hy : yy q i b t = true) :
    twoB (SS q i b j1) (proj i (V q t)) = (Ab q i b j1 t && Bb q i b j1 t) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  constructor
  · intro h2
    obtain ⟨h1t, htj, hym, hyp⟩ := two_both hi hj ht hy h2
    refine ⟨?_, inP_of htj hyp⟩
    unfold Ab; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h1t, inP_of (by omega) hym⟩
  · rintro ⟨hA, hB⟩
    obtain ⟨a, ha, h1, e1⟩ := prev_nb hi hj ht hy hA
    obtain ⟨a', ha', h1', e1'⟩ := next_nb hi hj ht hy hB
    have hne : a ≠ a' := by
      intro e; subst e
      unfold Ab at hA; simp only [Bool.and_eq_true, decide_eq_true_eq] at hA
      have := INJ (q := q) (i := i) (b := b) (j1 := j1) hi hj (t := t - 1) (t' := t + 1) (by omega)
        (inP_yy hB).1 (inP_yy hA.2).2 (inP_yy hB).2 (e1.trans e1'.symm)
      omega
    rw [twoB_iff]
    by_cases hl : a < a'
    · exact ⟨a, a', hl, ha', h1, h1'⟩
    · exact ⟨a', a, by omega, ha, h1', h1⟩

theorem endW_at (hi : i < 9) (hj : j1 ≤ M) {t : Nat} (ht : t ≤ j1) (hy : yy q i b t = true) :
    endW (SS q i b j1) (proj i (V q t)) =
      (if Ab q i b j1 t then 0 else 1) + (if Bb q i b j1 t then 0 else 1) := by
  unfold endW
  rw [two_char hi hj ht hy, any_char hi hj ht hy, (SS_iff q i b j1 _).mpr ⟨t, ht, hy, rfl⟩]
  cases Ab q i b j1 t <;> cases Bb q i b j1 t <;> rfl

theorem cnt_single (hi : i < 9) (hj : j1 ≤ M) {u : Nat} (hs : SS q i b j1 u = true) :
    cnt (j1 + 1) (fun t => yy q i b t && proj i (V q t) == u) = 1 := by
  have h1 : cnt (j1 + 1) (fun t => yy q i b t && proj i (V q t) == u) ≤ 1 := by
    apply cnt_le_one; intro t t' ht ht' p p'
    simp only [Bool.and_eq_true, beq_iff_eq] at p p'
    exact INJ hi hj (by omega) (by omega) p.1 p'.1 (p.2.trans p'.2.symm)
  obtain ⟨t, ht, hy, e⟩ := (SS_iff q i b j1 _).mp hs
  have h2 := cnt_pos (T := j1 + 1) (p := fun t => yy q i b t && proj i (V q t) == u) (t := t) (by omega)
    (by simp [hy, e])
  omega

theorem reidx (hi : i < 9) (hj : j1 ≤ M) (F : Nat → Nat) (hF0 : ∀ u, SS q i b j1 u = false → F u = 0) :
    sm 256 F = sm (j1 + 1) (fun t => if yy q i b t then F (proj i (V q t)) else 0) := by
  apply sm_reindex 256 (j1 + 1) (yy q i b) (fun t => proj i (V q t)) F
  · intro t _ _; exact proj_lt hi (V_lt q t)
  · intro u _
    by_cases hs : SS q i b j1 u = true
    · rw [cnt_single hi hj hs]; simp
    · have : SS q i b j1 u = false := by cases h : SS q i b j1 u <;> simp_all
      rw [hF0 u this]; simp

theorem cnt_shift (n : Nat) (p : Nat → Bool) :
    cnt (n + 1) p = (if p 0 then 1 else 0) + cnt n (fun t => p (t + 1)) := by
  induction n with
  | zero => simp [cnt_succ]
  | succ n ih => rw [cnt_succ, ih, cnt_succ]; omega

theorem tele (y : Nat → Bool) : ∀ n, (if y n then 1 else 0) + cnt n (fun t => y t && !y (t + 1)) =
    (if y 0 then 1 else 0) + cnt n (fun t => y (t + 1) && !y t) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cnt_succ, cnt_succ]
    cases h1 : y n <;> cases h2 : y (n + 1) <;> simp_all <;> omega

theorem cnt_or_le (n : Nat) (p p' r : Nat → Bool) (hd : ∀ t, t < n → p t = true → p' t = true → False)
    (hr : ∀ t, t < n → (p t || p' t) = true → r t = true) : cnt n p + cnt n p' ≤ cnt n r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cnt_succ, cnt_succ, cnt_succ]
    have := ih (fun t ht => hd t (by omega)) (fun t ht => hr t (by omega))
    have hdn := hd n (by omega); have hrn := hr n (by omega)
    cases h1 : p n <;> cases h2 : p' n <;> cases h3 : r n <;> simp_all <;> omega

def outF (q : Snake M) (i : Nat) (b : Bool) (t : Nat) : Bool := yy q i b t && !yy q i b (t + 1)
def innF (q : Snake M) (i : Nat) (b : Bool) (t : Nat) : Bool := yy q i b (t + 1) && !yy q i b t

theorem ends_ok (hi : i < 9) (hj : j1 ≤ M) (hyj : yy q i b j1 = true) (hk : cnt M (dif q i) ≤ 25) :
    sm 256 (endW (SS q i b j1)) ≤ 26 := by
  rw [reidx (q := q) (b := b) hi hj _ (by intro u hu; unfold endW; rw [hu]; rfl)]
  have hcg : ∀ t, t < j1 + 1 → (if yy q i b t then endW (SS q i b j1) (proj i (V q t)) else 0) =
      (fun t => (if (yy q i b t && !Ab q i b j1 t) then 1 else 0) +
      (if (yy q i b t && !Bb q i b j1 t) then 1 else 0)) t := by
    intro t ht
    by_cases hy : yy q i b t = true
    · rw [if_pos hy, endW_at hi hj (by omega) hy]; simp only [hy, Bool.true_and]
      cases Ab q i b j1 t <;> cases Bb q i b j1 t <;> rfl
    · have : yy q i b t = false := by cases h : yy q i b t <;> simp_all
      simp [this]
  rw [sm_congr hcg]
  rw [sm_add]
  show cnt (j1 + 1) (fun t => yy q i b t && !Ab q i b j1 t) + cnt (j1 + 1) (fun t => yy q i b t && !Bb q i b j1 t) ≤ 26
  have hB : cnt (j1 + 1) (fun t => yy q i b t && !Bb q i b j1 t) = cnt j1 (outF q i b) + 1 := by
    rw [cnt_succ]
    have : Bb q i b j1 j1 = false := by
      unfold Bb inP; cases h : yy q i b (j1 + 1) <;> simp
    rw [this, hyj]; simp only [Bool.not_false, Bool.and_self, if_true]
    congr 1; unfold cnt; apply sm_congr; intro t ht
    unfold Bb inP outF; simp [show t + 1 ≤ j1 by omega]
  have hA : cnt (j1 + 1) (fun t => yy q i b t && !Ab q i b j1 t) =
      (if yy q i b 0 then 1 else 0) + cnt j1 (innF q i b) := by
    rw [cnt_shift]
    have : Ab q i b j1 0 = false := by unfold Ab; simp
    rw [this]; simp only [Bool.not_false, Bool.and_true]
    congr 1; unfold cnt; apply sm_congr; intro t ht
    unfold Ab inP innF; simp [show t ≤ j1 by omega]
  have ht : (if yy q i b j1 then 1 else 0) + cnt j1 (outF q i b) =
      (if yy q i b 0 then 1 else 0) + cnt j1 (innF q i b) := tele (yy q i b) j1
  rw [hyj] at ht
  have hc : cnt j1 (outF q i b) + cnt j1 (innF q i b) ≤ cnt j1 (dif q i) :=
    cnt_or_le j1 _ _ (dif q i) (by intro t _ h1 h2; unfold outF at h1; unfold innF at h2; simp_all) (by
      intro t _ h
      unfold dif; unfold outF innF yy at h
      cases e1 : (V q t).testBit i <;> cases e2 : (V q (t + 1)).testBit i <;> cases b <;> simp_all)
  have hm := cnt_mono (dif q i) hj
  have h0 : (if yy q i b 0 then 1 else 0) ≤ 1 := by split <;> omega
  simp only [if_true] at ht
  omega

theorem card_ok (hi : i < 9) (hj : j1 ≤ M) : cnt 256 (SS q i b j1) = cnt (j1 + 1) (yy q i b) := by
  unfold cnt
  rw [reidx (q := q) (b := b) hi hj _ (by intro u hu; simp [hu])]
  apply sm_congr; intro t ht
  by_cases hy : yy q i b t = true
  · rw [(SS_iff q i b j1 _).mpr ⟨t, by omega, hy, rfl⟩]; simp [hy]
  · have : yy q i b t = false := by cases h : yy q i b t <;> simp_all
    simp [this]

end Dim8Lift
