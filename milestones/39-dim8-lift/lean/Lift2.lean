import Lift1
/-! Part 2: the half of the snake prefix in the facet `bit i = b`, as a vertex set of Q8. -/
set_option linter.deprecated false
namespace Dim8Lift
open Snake9

variable {M : Nat} (q : Snake M) (i : Nat) (b : Bool) (j1 : Nat)

def yy (t : Nat) : Bool := (V q t).testBit i == b

def SS (u : Nat) : Bool := (List.range (j1 + 1)).any (fun t => yy q i b t && proj i (V q t) == u)

theorem SS_iff (u : Nat) : SS q i b j1 u = true ↔ ∃ t, t ≤ j1 ∧ yy q i b t = true ∧ proj i (V q t) = u := by
  unfold SS; rw [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, h⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨t, by simp at ht; omega, h.1, h.2⟩
  · rintro ⟨t, ht, hy, hp⟩
    exact ⟨t, by simp; omega, by simp [hy, hp]⟩

theorem yy_bit {t : Nat} (h : yy q i b t = true) : (V q t).testBit i = b := by
  unfold yy at h; simpa using h

variable {q i b j1}

theorem half_eq_flip (hi : i < 9) {t t' a : Nat} (ha : a < 8) (hy : yy q i b t = true) (hy' : yy q i b t' = true)
    (e : proj i (V q t') = proj i (V q t) ^^^ 2 ^ a) : V q t' = V q t ^^^ 2 ^ (sh i a) := by
  have h1 := emb_proj hi (V_lt q t')
  have h2 := emb_proj hi (q9_lt (V_lt q t) (k := sh i a) (by unfold sh; split <;> omega))
  rw [yy_bit q i b hy', e] at h1
  rw [proj_flip hi (V_lt q t) ha, bit_flip_sh hi (V_lt q t) ha, yy_bit q i b hy] at h2
  rw [← h1, h2]

theorem KA_to (hi : i < 9) (hj : j1 ≤ M) {t t' a : Nat} (ht : t ≤ j1) (ht' : t' ≤ j1) (ha : a < 8)
    (hy : yy q i b t = true) (hy' : yy q i b t' = true)
    (e : proj i (V q t') = proj i (V q t) ^^^ 2 ^ a) : t' = t + 1 ∨ t = t' + 1 :=
  V_adj q (by omega) (by omega) (by unfold sh; split <;> omega) (half_eq_flip hi ha hy hy' e)

theorem KA_from (hi : i < 9) (hj : j1 ≤ M) {t : Nat} (ht : t + 1 ≤ j1)
    (hy : yy q i b t = true) (hy' : yy q i b (t + 1) = true) :
    ∃ a, a < 8 ∧ proj i (V q (t + 1)) = proj i (V q t) ^^^ 2 ^ a := by
  obtain ⟨k, hk, e⟩ := V_step q (t := t) (by omega)
  have hki : k ≠ i := by
    intro hki; subst hki
    have h := bit_flip hk (V_lt q t) hk
    rw [← e, yy_bit q k b hy, yy_bit q k b hy'] at h
    simp at h
  obtain ⟨a, ha, hs⟩ := sh_cover hi hk hki
  exact ⟨a, ha, by rw [e, ← hs, proj_flip hi (V_lt q t) ha]⟩

theorem KA_from' (hi : i < 9) (hj : j1 ≤ M) {t : Nat} (ht : t + 1 ≤ j1)
    (hy : yy q i b t = true) (hy' : yy q i b (t + 1) = true) :
    ∃ a, a < 8 ∧ proj i (V q t) = proj i (V q (t + 1)) ^^^ 2 ^ a := by
  obtain ⟨a, ha, e⟩ := KA_from hi hj ht hy hy'
  exact ⟨a, ha, by rw [e, q8_xx (proj_lt hi (V_lt q t)) ha]⟩

theorem INJ (hi : i < 9) (hj : j1 ≤ M) {t t' : Nat} (ht : t ≤ j1) (ht' : t' ≤ j1)
    (hy : yy q i b t = true) (hy' : yy q i b t' = true) (e : proj i (V q t) = proj i (V q t')) : t = t' := by
  apply V_inj q (by omega) (by omega)
  rw [← emb_proj hi (V_lt q t), ← emb_proj hi (V_lt q t'), e, yy_bit q i b hy, yy_bit q i b hy']

/-- A neighbour of a half vertex inside the half comes from the previous or next snake vertex. -/
theorem NBR (hi : i < 9) (hj : j1 ≤ M) {t a : Nat} (ht : t ≤ j1) (hy : yy q i b t = true) (ha : a < 8)
    (hs : SS q i b j1 (proj i (V q t) ^^^ 2 ^ a) = true) :
    ∃ t', t' ≤ j1 ∧ yy q i b t' = true ∧ proj i (V q t') = proj i (V q t) ^^^ 2 ^ a ∧
      (t' = t + 1 ∨ t = t' + 1) := by
  obtain ⟨t', ht', hy', e⟩ := (SS_iff q i b j1 _).mp hs
  exact ⟨t', ht', hy', e, KA_to hi hj ht ht' ha hy hy' e⟩

theorem deg_ok (hi : i < 9) (hj : j1 ≤ M) {u a c d : Nat} (hu : u < 256) (hac : a < c) (hcd : c < d) (hd : d < 8)
    (h0 : SS q i b j1 u = true) (h1 : SS q i b j1 (u ^^^ 2 ^ a) = true)
    (h2 : SS q i b j1 (u ^^^ 2 ^ c) = true) : SS q i b j1 (u ^^^ 2 ^ d) = false := by
  cases h3 : SS q i b j1 (u ^^^ 2 ^ d)
  · rfl
  · exfalso
    obtain ⟨t, ht, hy, rfl⟩ := (SS_iff q i b j1 _).mp h0
    obtain ⟨ta, hta, hya, ea, sa⟩ := NBR hi hj ht hy (by omega) h1
    obtain ⟨tc, htc, hyc, ec, sc⟩ := NBR hi hj ht hy (by omega) h2
    obtain ⟨td, htd, hyd, ed, sd⟩ := NBR hi hj ht hy hd h3
    have nac : ta ≠ tc := by
      intro e; subst e; exact q8_ne hu (by omega) (by omega) (by omega) (ea.symm.trans ec)
    have ncd : tc ≠ td := by
      intro e; subst e; exact q8_ne hu (by omega) (by omega) (by omega) (ec.symm.trans ed)
    have nad : ta ≠ td := by
      intro e; subst e; exact q8_ne hu (by omega) (by omega) (by omega) (ea.symm.trans ed)
    omega

end Dim8Lift
