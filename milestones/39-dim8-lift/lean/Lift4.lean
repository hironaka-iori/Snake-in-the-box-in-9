import Lift3
import Premise
/-! Part 4: the half of a snake prefix is a `Pit`; the reduction theorem. -/
set_option linter.deprecated false
namespace Dim8Lift
open Snake9

theorem twoB_iff (S : Nat → Bool) (u : Nat) : twoB S u = true ↔
    ∃ a a', a < a' ∧ a' < 8 ∧ S (nb u a) = true ∧ S (nb u a') = true := by
  unfold twoB; simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, _, a', ha', ⟨h1, h2⟩, h3⟩; exact ⟨a, a', h1, ha', h2, h3⟩
  · rintro ⟨a, a', h1, ha', h2, h3⟩; exact ⟨a, by omega, a', ha', ⟨h1, h2⟩, h3⟩

theorem anyB_iff (S : Nat → Bool) (u : Nat) : anyB S u = true ↔ ∃ a, a < 8 ∧ S (nb u a) = true := by
  unfold anyB; simp only [List.any_eq_true, List.mem_range]

variable {M : Nat} {q : Snake M} {i : Nat} {b : Bool} {j1 : Nat}

def tOf (q : Snake M) (i : Nat) (b : Bool) (j1 u : Nat) : Nat :=
  ((List.range (j1 + 1)).find? (fun t => yy q i b t && proj i (V q t) == u)).getD 0

theorem tOf_eq (hi : i < 9) (hj : j1 ≤ M) {t : Nat} (ht : t ≤ j1) (hy : yy q i b t = true) :
    tOf q i b j1 (proj i (V q t)) = t := by
  unfold tOf
  cases h : (List.range (j1 + 1)).find? (fun t' => yy q i b t' && proj i (V q t') == proj i (V q t)) with
  | none =>
    have := List.find?_eq_none.mp h t (by simp; omega)
    simp [hy] at this
  | some t0 =>
    have hp := List.find?_some h
    have hm := List.mem_of_find?_eq_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    simp at hm
    simp only [Option.getD_some]
    exact INJ hi hj (by omega) ht hp.1 hy hp.2

def ell (q : Snake M) (i : Nat) (b : Bool) (j1 u : Nat) : Nat :=
  if SS q i b j1 u then lv q i b j1 (tOf q i b j1 u) else 64

theorem ell_at (hi : i < 9) (hj : j1 ≤ M) {t : Nat} (ht : t ≤ j1) (hy : yy q i b t = true) :
    ell q i b j1 (proj i (V q t)) = lv q i b j1 t := by
  unfold ell
  rw [if_pos ((SS_iff q i b j1 _).mpr ⟨t, ht, hy, rfl⟩), tOf_eq hi hj ht hy]

/-- Both path neighbours of a half vertex with two half neighbours lie in the half. -/
theorem two_both (hi : i < 9) (hj : j1 ≤ M) {t : Nat} (ht : t ≤ j1) (hy : yy q i b t = true)
    (h2 : twoB (SS q i b j1) (proj i (V q t)) = true) :
    1 ≤ t ∧ t + 1 ≤ j1 ∧ yy q i b (t - 1) = true ∧ yy q i b (t + 1) = true := by
  obtain ⟨a, a', haa, ha', h1, h1'⟩ := (twoB_iff _ _).mp h2
  have hu := proj_lt hi (V_lt q t)
  obtain ⟨ta, hta, hya, ea, sa⟩ := NBR hi hj ht hy (by omega) h1
  obtain ⟨tb, htb, hyb, eb, sb⟩ := NBR hi hj ht hy ha' h1'
  have nab : ta ≠ tb := by
    intro e; subst e; exact q8_ne hu (by omega) ha' (by omega) (ea.symm.trans eb)
  rcases sa with sa | sa <;> rcases sb with sb | sb
  · omega
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · have : t - 1 = tb := by omega
      rw [this]; exact hyb
    · rw [← sa]; exact hya
  · refine ⟨by omega, by omega, ?_, ?_⟩
    · have : t - 1 = ta := by omega
      rw [this]; exact hya
    · rw [← sb]; exact hyb
  · omega

theorem lvl_ok (hi : i < 9) (hj : j1 ≤ M) (hL : cnt (j1 + 1) (yy q i b) ≤ 116) {u : Nat} (hu : u < 256)
    (h2 : twoB (SS q i b j1) u = true) :
    ∃ a, a < 8 ∧ SS q i b j1 (nb u a) = true ∧ ell q i b j1 (nb u a) < ell q i b j1 u := by
  by_cases hs : SS q i b j1 u = true
  · obtain ⟨t, ht, hy, rfl⟩ := (SS_iff q i b j1 _).mp hs
    obtain ⟨h1t, htj, hym, hyp⟩ := two_both hi hj ht hy h2
    have hpm : inP q i b j1 (t - 1) = true := inP_of (by omega) hym
    have hpp : inP q i b j1 (t + 1) = true := inP_of htj hyp
    have hsR : sR (inP q i b j1) t = sR (inP q i b j1) (t - 1) := by
      have e : t = (t - 1) + 1 := by omega
      conv => lhs; rw [e]
      exact sR_step _ _ hpm
    have hsle := sR_le (inP q i b j1) (t - 1)
    have heR : eR q i b j1 t = eR q i b j1 (t + 1) := eR_step htj hpp
    have heR' : eR q i b j1 (t - 1) = eR q i b j1 t := by
      have e : t = (t - 1) + 1 := by omega
      have := eR_step (q := q) (i := i) (b := b) (j1 := j1) (t := t - 1) (by omega)
        (by rw [← e]; exact inP_of ht hy)
      rw [this, ← e]
    have hge := eR_ge (q := q) (i := i) (b := b) htj
    have hsRp : sR (inP q i b j1) (t + 1) = sR (inP q i b j1) t := sR_step _ _ (inP_of ht hy)
    by_cases hc : t - sR (inP q i b j1) t ≤ eR q i b j1 t - t
    · obtain ⟨a, ha, e⟩ := KA_from' (q := q) (i := i) (b := b) (j1 := j1) (t := t - 1) hi hj (by omega) hym
        (by have : t - 1 + 1 = t := by omega
            rw [this]; exact hy)
      have e' : proj i (V q (t - 1)) = proj i (V q t) ^^^ 2 ^ a := by
        have : t - 1 + 1 = t := by omega
        rw [this] at e; exact e
      refine ⟨a, ha, ?_, ?_⟩
      · show SS q i b j1 (proj i (V q t) ^^^ 2 ^ a) = true
        rw [← e']; exact (SS_iff q i b j1 _).mpr ⟨t - 1, by omega, hym, rfl⟩
      · show ell q i b j1 (proj i (V q t) ^^^ 2 ^ a) < ell q i b j1 (proj i (V q t))
        rw [← e', ell_at hi hj (by omega) hym, ell_at hi hj ht hy]
        unfold lv; rw [Nat.min_def, Nat.min_def, heR', ← hsR]; split <;> (try split) <;> omega
    · obtain ⟨a, ha, e⟩ := KA_from (q := q) (i := i) (b := b) (j1 := j1) (t := t) hi hj htj hy hyp
      refine ⟨a, ha, ?_, ?_⟩
      · show SS q i b j1 (proj i (V q t) ^^^ 2 ^ a) = true
        rw [← e]; exact (SS_iff q i b j1 _).mpr ⟨t + 1, htj, hyp, rfl⟩
      · show ell q i b j1 (proj i (V q t) ^^^ 2 ^ a) < ell q i b j1 (proj i (V q t))
        rw [← e, ell_at hi hj htj hyp, ell_at hi hj ht hy]
        unfold lv; rw [Nat.min_def, Nat.min_def, ← heR, hsRp]; split <;> (try split) <;> omega
  · obtain ⟨a, a', _, ha', h1, _⟩ := (twoB_iff _ _).mp h2
    refine ⟨a, by omega, h1, ?_⟩
    obtain ⟨t, ht, hy, e⟩ := (SS_iff q i b j1 _).mp h1
    have hf : SS q i b j1 u = false := by cases h : SS q i b j1 u <;> simp_all
    rw [← e, ell_at hi hj ht hy]
    unfold ell; rw [hf]
    have := lv_bound (q := q) (i := i) (b := b) ht hy
    simp; omega

end Dim8Lift
