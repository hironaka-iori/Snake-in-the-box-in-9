import CubeBridge2
/-! Bridge, part 3: definition clauses and cycle clauses. -/
set_option linter.deprecated false
set_option maxRecDepth 100000
namespace Dim8Lift.Cube
open Dim8Lift.Cnf Snake9.LocalWindow

variable {τ : Nat → Bool} {S : Nat → Bool} {ℓ : Nat → Nat}

theorem pos_v {v : Nat} (h : 0 < v) : litTrue τ (pos v) = τ v := litTrue_pos τ h

theorem defU_ok (hd : Dec τ S ℓ) {u : Nat} (hu : u < 256) : ∀ c ∈ defU u, clauseTrue τ c = true := by
  have vp : ∀ a b, 0 < pV u a b := by intro a b; unfold pV; omega
  have vs : ∀ i, 0 < sV i := by intro i; unfold sV; omega
  have vt : 0 < twoV u := by unfold twoV; omega
  have va : 0 < anyV u := by unfold anyV; omega
  have v1 : 0 < e1V u := by unfold e1V; omega
  have v0 : 0 < e0V u := by unfold e0V; omega
  intro c hc
  unfold defU at hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · simp only [List.mem_flatMap] at hc
      obtain ⟨⟨a, b⟩, hab, hc⟩ := hc
      rw [mem_pairs8] at hab
      have ha := fx_lt hu (show a < 8 by omega); have hb := fx_lt hu hab.2
      simp only [defPair, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;>
        simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] <;>
        simp only [ln (vp _ _), lp (vp _ _), ln (vs _), lp (vs _), lp vt, hd.p u a b hu (by omega) hab.2,
          hd.s _ ha, hd.s _ hb, hd.two u hu]
      · cases S (fx u a) <;> simp
      · cases S (fx u a) <;> cases S (fx u b) <;> simp
      · cases S (fx u a) <;> cases S (fx u b) <;> simp
      · cases h1 : S (fx u a) <;> cases h2 : S (fx u b) <;> simp
        exact (twoB_iff S u).mpr ⟨a, b, hab.1, hab.2, h1, h2⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · simp only [defTwo, clauseTrue, List.any_cons, Bool.or_eq_true]
        rw [ln vt, hd.two u hu]
        cases h2 : twoB S u
        · simp
        · obtain ⟨a, b, hab, hb, h1, h1'⟩ := (twoB_iff S u).mp h2
          right; rw [List.any_eq_true]
          refine ⟨pos (pV u a b), List.mem_map.mpr ⟨(a, b), mem_pairs8.mpr ⟨hab, hb⟩, rfl⟩, ?_⟩
          rw [lp (vp _ _), hd.p u a b hu (by omega) hb]
          unfold fx; unfold nb at h1 h1'; simp [h1, h1']
      · simp only [List.mem_map, List.mem_range] at hc
        obtain ⟨a, ha, rfl⟩ := hc
        simp only [defAny1, clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
        rw [ln (vs _), lp va, hd.s _ (fx_lt hu ha), hd.any u hu]
        cases h : S (fx u a)
        · simp
        · right; exact (anyB_iff S u).mpr ⟨a, ha, h⟩
  · rcases List.mem_cons.mp hc with rfl | hc
    · simp only [defAny, clauseTrue, List.any_cons, Bool.or_eq_true]
      rw [ln va, hd.any u hu]
      cases h2 : anyB S u
      · simp
      · obtain ⟨a, ha, h1⟩ := (anyB_iff S u).mp h2
        right; rw [List.any_eq_true]
        refine ⟨pos (sV (fx u a)), List.mem_map.mpr ⟨a, List.mem_range.mpr ha, rfl⟩, ?_⟩
        rw [lp (vs _), hd.s _ (fx_lt hu ha)]; exact h1
    · simp only [defE, List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] <;>
        simp only [ln v1, lp v1, ln v0, lp v0, ln (vs _), lp (vs _), ln vt, lp vt, ln va, lp va,
          hd.e1 u hu, hd.e0 u hu, hd.s u hu, hd.two u hu, hd.any u hu] <;>
        cases S u <;> cases twoB S u <;> cases anyB S u <;> simp

theorem fam_def (hd : Dec τ S ℓ) : ∀ c ∈ famDef, clauseTrue τ c = true := by
  intro c hc
  simp only [famDef, List.mem_flatMap] at hc
  obtain ⟨u, hu, hc⟩ := hc
  exact defU_ok hd (mem_R256.mp hu) c hc

/-! ### Cycles -/

theorem deg3 {c' L D : Nat} (hp : Pit c' L D S ℓ) {u a b d : Nat} (hu : u < 256) (ha : a < 8) (hb : b < 8)
    (hd : d < 8) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (h0 : S u = true) (h1 : S (nb u a) = true)
    (h2 : S (nb u b) = true) (h3 : S (nb u d) = true) : False := by
  have key : ∀ x y z, x < y → y < z → z < 8 → S (nb u x) = true → S (nb u y) = true → S (nb u z) = true → False := by
    intro x y z hxy hyz hz hx hy hz'
    have := hp.deg u hu x y z hxy hyz hz h0 hx hy; rw [this] at hz'; exact absurd hz' (by simp)
  -- sort a, b, d
  rcases Nat.lt_or_gt_of_ne hab with h | h <;> rcases Nat.lt_or_gt_of_ne had with h' | h' <;>
    rcases Nat.lt_or_gt_of_ne hbd with h'' | h''
  · exact key a b d h h'' hd h1 h2 h3
  · exact key a d b h' h'' hb h1 h3 h2
  · omega
  · exact key d a b h' h hb h3 h1 h2
  · exact key b a d h h' hd h2 h1 h3
  · omega
  · exact key b d a h'' h' ha h2 h3 h1
  · exact key d b a h'' h ha h3 h2 h1

/-- A list of selected vertices in which every vertex has two neighbours in the list (in different
directions) cannot exist: a vertex of least level would need a smaller neighbour inside the list. -/
theorem no_sel_cycle {c' L D : Nat} (hp : Pit c' L D S ℓ) (C : List Nat)
    (hC : ∀ v ∈ C, v < 256 ∧ ∃ a b, a ≠ b ∧ a < 8 ∧ b < 8 ∧ nb v a ∈ C ∧ nb v b ∈ C)
    (hsel : ∀ v ∈ C, S v = true) : ∀ n, ∀ v ∈ C, ℓ v ≤ n → False := by
  intro n
  induction n with
  | zero =>
    intro v hv hl
    obtain ⟨hv256, a, b, hab, ha, hb, hma, hmb⟩ := hC v hv
    have h2 : twoB S v = true := by
      rcases Nat.lt_or_gt_of_ne hab with h | h
      · exact (twoB_iff S v).mpr ⟨a, b, h, hb, hsel _ hma, hsel _ hmb⟩
      · exact (twoB_iff S v).mpr ⟨b, a, h, ha, hsel _ hmb, hsel _ hma⟩
    obtain ⟨d, _, _, hl'⟩ := hp.lvl v hv256 h2
    omega
  | succ n ih =>
    intro v hv hl
    obtain ⟨hv256, a, b, hab, ha, hb, hma, hmb⟩ := hC v hv
    have h2 : twoB S v = true := by
      rcases Nat.lt_or_gt_of_ne hab with h | h
      · exact (twoB_iff S v).mpr ⟨a, b, h, hb, hsel _ hma, hsel _ hmb⟩
      · exact (twoB_iff S v).mpr ⟨b, a, h, ha, hsel _ hmb, hsel _ hma⟩
    obtain ⟨d, hd8, hsd, hl'⟩ := hp.lvl v hv256 h2
    by_cases hda : d = a
    · subst hda; exact ih _ hma (by omega)
    · by_cases hdb : d = b
      · subst hdb; exact ih _ hmb (by omega)
      · exact deg3 hp hv256 ha hb hd8 hab (Ne.symm hda) (Ne.symm hdb) (hsel v hv) (hsel _ hma) (hsel _ hmb) hsd

theorem xx (u a : Nat) : (u ^^^ 2 ^ a) ^^^ 2 ^ a = u := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
theorem xsw (u a b : Nat) : (u ^^^ 2 ^ a) ^^^ 2 ^ b = (u ^^^ 2 ^ b) ^^^ 2 ^ a := by
  rw [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_comm (2 ^ a)]

theorem fam_c4 {c' L D : Nat} (hp : Pit c' L D S ℓ) (hd : Dec τ S ℓ) : ∀ c ∈ famC4, clauseTrue τ c = true := by
  intro c hc
  simp only [famC4, List.mem_flatMap, List.mem_filterMap] at hc
  obtain ⟨u, hu, ⟨a, b⟩, hab, hc⟩ := hc
  rw [mem_R256] at hu; rw [mem_pairs8] at hab
  split at hc
  · exact absurd hc (by simp)
  · simp only [Option.some.injEq] at hc; subst hc
    have vs : ∀ i, 0 < sV i := by intro i; unfold sV; omega
    have h1 := fx_lt hu (show a < 8 by omega); have h2 := fx_lt hu hab.2
    have h3 := fx_lt h1 hab.2
    simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
    rw [ln (vs _), ln (vs _), ln (vs _), ln (vs _), hd.s u hu, hd.s _ h1, hd.s _ h3, hd.s _ h2]
    apply Classical.byContradiction; intro hn
    simp only [not_or, Bool.not_eq_true', Bool.not_eq_false'] at hn
    have hC := no_sel_cycle hp [u, fx u a, fx (fx u a) b, fx u b] (by
      intro v hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      have e1 : nb (fx u a) a = u := xx u a
      have e2 : nb (fx (fx u a) b) b = fx u a := xx (fx u a) b
      have e3 : nb (fx (fx u a) b) a = fx u b := by unfold nb fx; rw [xsw, xx]
      have e4 : nb (fx u b) b = u := xx u b
      have e5 : nb (fx u b) a = fx (fx u a) b := by unfold nb fx; rw [xsw]
      have e6 : nb u a = fx u a := rfl
      have e7 : nb u b = fx u b := rfl
      have e8 : nb (fx u a) b = fx (fx u a) b := rfl
      rcases hv with rfl | rfl | rfl | rfl
      · exact ⟨hu, a, b, by omega, by omega, hab.2, by rw [e6]; simp, by rw [e7]; simp⟩
      · exact ⟨h1, a, b, by omega, by omega, hab.2, by rw [e1]; simp, by rw [e8]; simp⟩
      · exact ⟨h3, a, b, by omega, by omega, hab.2, by rw [e3]; simp, by rw [e2]; simp⟩
      · exact ⟨h2, a, b, by omega, by omega, hab.2, by rw [e5]; simp, by rw [e4]; simp⟩) (by
      intro v hv
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> simp_all) (ℓ u) u (by simp) (Nat.le_refl _)
    exact hC

end Dim8Lift.Cube
