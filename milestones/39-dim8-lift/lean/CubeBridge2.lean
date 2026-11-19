import CubeBridge1
/-! Bridge, part 2: the fixed, degree, level and definition families hold under any assignment that
decodes like `tau0`. -/
set_option linter.deprecated false
namespace Dim8Lift.Cube
open Dim8Lift.Cnf Snake9.LocalWindow

structure Dec (τ : Nat → Bool) (S : Nat → Bool) (ℓ : Nat → Nat) : Prop where
  s : ∀ u, u < 256 → τ (sV u) = S u
  o : ∀ u j, u < 256 → 1 ≤ j → j ≤ 64 → τ (oV u j) = decide (j ≤ ℓ u)
  a : ∀ u i j, u < 256 → i < 8 → 1 ≤ j → j ≤ 64 → τ (aV u i j) = (S (fx u i) && !decide (j ≤ ℓ (fx u i)))
  p : ∀ u a b, u < 256 → a < 8 → b < 8 → τ (pV u a b) = (S (fx u a) && S (fx u b))
  two : ∀ u, u < 256 → τ (twoV u) = twoB S u
  any : ∀ u, u < 256 → τ (anyV u) = anyB S u
  e1 : ∀ u, u < 256 → τ (e1V u) = (S u && !twoB S u)
  e0 : ∀ u, u < 256 → τ (e0V u) = (S u && !anyB S u)

theorem mem_R256 {u : Nat} : u ∈ R256 ↔ u < 256 := by simp [R256]
theorem mem_pairs8 {a b : Nat} : (a, b) ∈ pairs8 ↔ a < b ∧ b < 8 := by
  simp only [pairs8, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, y, ⟨hy, hxy⟩, h1, h2⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨a, by omega, b, ⟨h2, h1⟩, rfl, rfl⟩
theorem mem_triples8 {a b c : Nat} : (a, b, c) ∈ triples8 ↔ a < b ∧ b < c ∧ c < 8 := by
  simp only [triples8, pairs8, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a', b'⟩, ⟨x, hx, y, ⟨hy, hxy⟩, h1⟩, z, ⟨hz, hyz⟩, h2⟩
    simp only [Prod.mk.injEq] at h1 h2; omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(a, b), ⟨a, by omega, b, ⟨by omega, h1⟩, rfl⟩, c, ⟨h3, h2⟩, rfl, rfl, rfl⟩

theorem fx_lt {u i : Nat} (hu : u < 256) (hi : i < 8) : fx u i < 256 := q8_lt hu hi

variable {τ : Nat → Bool} {S : Nat → Bool} {ℓ : Nat → Nat}

theorem lp {v : Nat} (h : 0 < v) : litTrue τ (pos v) = τ v := litTrue_pos τ h
theorem ln {v : Nat} (h : 0 < v) : litTrue τ (neg v) = !τ v := litTrue_neg τ h

theorem fam_fix (hd : Dec τ S ℓ) (A : Nat) (hA : ∀ u, u < 64 → S u = A.testBit u) :
    ∀ c ∈ famFix A, clauseTrue τ c = true := by
  intro c hc
  simp only [famFix, List.mem_map, List.mem_range] at hc
  obtain ⟨u, hu, rfl⟩ := hc
  have hs := hd.s u (by omega); rw [hA u hu] at hs
  split <;> simp_all [clauseTrue, lp, ln, sV]

theorem fam_deg {c' L D : Nat} (hp : Pit c' L D S ℓ) (hd : Dec τ S ℓ) : ∀ c ∈ famDeg, clauseTrue τ c = true := by
  intro c hc
  simp only [famDeg, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨u, hu, ⟨a, b, d⟩, ht, rfl⟩ := hc
  rw [mem_R256] at hu; rw [mem_triples8] at ht
  have h := hp.deg u hu a b d ht.1 ht.2.1 ht.2.2
  simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
  rw [ln (by unfold sV; omega), ln (by unfold sV; omega), ln (by unfold sV; omega), ln (by unfold sV; omega),
    hd.s u hu, hd.s _ (fx_lt hu (by omega)), hd.s _ (fx_lt hu (by omega)), hd.s _ (fx_lt hu (by omega))]
  unfold fx; unfold nb at h
  cases h0 : S u <;> cases h1 : S (u ^^^ 2 ^ a) <;> cases h2 : S (u ^^^ 2 ^ b) <;> simp_all

theorem lvlU_ok {c' L : Nat} (hp : Pit c' L 64 S ℓ) (hd : Dec τ S ℓ) {u : Nat} (hu : u < 256) :
    ∀ c ∈ lvlU u, clauseTrue τ c = true := by
  have v0 : ∀ i j, 0 < oV i j := by intro i j; unfold oV; omega
  have v1 : ∀ i i' j, 0 < aV i i' j := by intro i i' j; unfold aV; omega
  have v2 : ∀ i, 0 < sV i := by intro i; unfold sV; omega
  have v3 : ∀ i, 0 < twoV i := by intro i; unfold twoV; omega
  intro c hc
  unfold lvlU at hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · simp only [lvlMono, List.mem_map, List.mem_range] at hc
      obtain ⟨j0, hj0, rfl⟩ := hc
      simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
      rw [ln (v0 _ _), lp (v0 _ _), hd.o u _ hu (by omega) (by omega), hd.o u _ hu (by omega) (by omega)]
      simp; omega
    · simp only [lvlAux, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff, or_false] at hc
      obtain ⟨i, hi, j0, hj0, hc⟩ := hc
      have hfx := fx_lt hu hi
      rcases hc with rfl | rfl
      · simp only [lvlA1, clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
        rw [ln (v1 _ _ _), lp (v2 _), hd.a u i _ hu hi (by omega) (by omega), hd.s _ hfx]
        cases S (fx u i) <;> simp
      · simp only [lvlA2, clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
        rw [ln (v1 _ _ _), ln (v0 _ _), hd.a u i _ hu hi (by omega) (by omega), hd.o _ _ hfx (by omega) (by omega)]
        cases S (fx u i) <;> simp <;> omega
  · rcases List.mem_cons.mp hc with rfl | hc
    · simp only [lvlOne, clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
      rw [ln (v3 _), lp (v0 _ _), hd.two u hu, hd.o u 1 hu (by omega) (by omega)]
      cases h2 : twoB S u
      · simp
      · obtain ⟨a, _, _, hl⟩ := hp.lvl u hu h2
        simp; omega
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨j0, hj0, rfl⟩ := hc
      unfold lvlStep
      simp only [clauseTrue, List.any_cons, List.any_append, Bool.or_eq_true]
      rw [ln (v3 _), hd.two u hu]
      cases h2 : twoB S u
      · simp
      · obtain ⟨a, ha, hsa, hl⟩ := hp.lvl u hu h2
        have hle := hp.lvl_le u hu
        by_cases hj : j0 + 1 < 64 ∧ j0 + 2 ≤ ℓ u
        · left; right
          rw [if_pos hj.1]; simp only [List.any_cons, List.any_nil, Bool.or_false]
          rw [lp (v0 _ _), hd.o u _ hu (by omega) (by omega)]; simp; omega
        · right
          rw [List.any_eq_true]
          refine ⟨pos (aV u a (j0 + 1)), List.mem_map.mpr ⟨a, List.mem_range.mpr ha, rfl⟩, ?_⟩
          rw [lp (v1 _ _ _), hd.a u a _ hu ha (by omega) (by omega)]
          unfold fx; unfold nb at hsa hl
          simp [hsa]; omega

theorem fam_lvl {c' L : Nat} (hp : Pit c' L 64 S ℓ) (hd : Dec τ S ℓ) : ∀ c ∈ famLvl, clauseTrue τ c = true := by
  intro c hc
  simp only [famLvl, List.mem_flatMap] at hc
  obtain ⟨u, hu, hc⟩ := hc
  exact lvlU_ok hp hd (mem_R256.mp hu) c hc

end Dim8Lift.Cube
