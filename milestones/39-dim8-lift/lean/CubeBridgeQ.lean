import CubeBridge5
/-! Bridge for the parent-pointer cube CNF `cubeCnfQ`. -/
set_option linter.deprecated false
namespace Dim8Lift.Cube
open Dim8Lift.Cnf Snake9.LocalWindow

variable {τ : Nat → Bool} {S : Nat → Bool} {ℓ : Nat → Nat}

theorem lvlQU_ok {c' L : Nat} (hp : Pit c' L 64 S ℓ) (hd : Dec0 τ S ℓ)
    (hq : ∀ u i, u < 256 → i < 8 → τ (qV u i) = (S (fx u i) && decide (ℓ (fx u i) < ℓ u)))
    {u : Nat} (hu : u < 256) : ∀ c ∈ lvlQU u, clauseTrue τ c = true := by
  have v0 : ∀ i j, 0 < oV i j := by intro i j; unfold oV; omega
  have vq : ∀ i j, 0 < qV i j := by intro i j; unfold qV; omega
  have v2 : ∀ i, 0 < sV i := by intro i; unfold sV; omega
  have v3 : ∀ i, 0 < twoV i := by intro i; unfold twoV; omega
  have hle := hp.lvl_le u hu
  intro c hc
  unfold lvlQU at hc
  rcases List.mem_append.mp hc with hc | hc
  · simp only [lvlMono, List.mem_map, List.mem_range] at hc
    obtain ⟨j0, hj0, rfl⟩ := hc
    simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
    rw [ln (v0 _ _), lp (v0 _ _), hd.o u _ hu (by omega) (by omega), hd.o u _ hu (by omega) (by omega)]
    simp; omega
  · rcases List.mem_cons.mp hc with rfl | hc
    · simp only [clauseTrue, List.any_cons, Bool.or_eq_true]
      rw [ln (v3 _), hd.two u hu]
      cases h2 : twoB S u
      · simp
      · obtain ⟨a, ha, hsa, hl⟩ := hp.lvl u hu h2
        right; rw [List.any_eq_true]
        refine ⟨pos (qV u a), List.mem_map.mpr ⟨a, List.mem_range.mpr ha, rfl⟩, ?_⟩
        rw [lp (vq _ _), hq u a hu ha]
        unfold fx; unfold nb at hsa hl; simp [hsa, hl]
    · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_map] at hc
      obtain ⟨i, hi, hc⟩ := hc
      have hf := fx_lt hu hi
      have hqi := hq u i hu hi
      rcases hc with rfl | rfl | rfl | ⟨j0, hj0, rfl⟩
      · simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
        rw [ln (vq _ _), lp (v2 _), hqi, hd.s _ hf]; cases S (fx u i) <;> simp
      · simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
        rw [ln (vq _ _), lp (v0 _ _), hqi, hd.o u 1 hu (by omega) (by omega)]
        cases S (fx u i) <;> simp <;> omega
      · simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
        rw [ln (vq _ _), ln (v0 _ _), hqi, hd.o _ 64 hf (by omega) (by omega)]
        cases S (fx u i) <;> simp <;> omega
      · simp only [clauseTrue, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
        rw [ln (vq _ _), ln (v0 _ _), lp (v0 _ _), hqi, hd.o _ _ hf (by omega) (by omega),
          hd.o u _ hu (by omega) (by omega)]
        cases S (fx u i) <;> simp <;> omega

theorem fam_lvlQ {c' L : Nat} (hp : Pit c' L 64 S ℓ) (hd : Dec0 τ S ℓ)
    (hq : ∀ u i, u < 256 → i < 8 → τ (qV u i) = (S (fx u i) && decide (ℓ (fx u i) < ℓ u))) :
    ∀ c ∈ famLvlQ, clauseTrue τ c = true := by
  intro c hc
  simp only [famLvlQ, List.mem_flatMap] at hc
  obtain ⟨u, hu, hc⟩ := hc
  exact lvlQU_ok hp hd hq (mem_R256.mp hu) c hc

theorem bridgeQ {c L A k : Nat} (hp : Pit c L 64 S ℓ) (hc : 1 ≤ c) (hL : L ≤ 255) (hk : 1 ≤ k)
    (hA : ∀ u, u < 64 → S u = A.testBit u) (hsub : ∀ q, ((subcubes.getD q []).filter S).length ≤ k) :
    cnfTrue (tauF S ℓ true c L k) (cubeCnfQ c L A k) = true := by
  have hd := dec0_tauF (S := S) (ℓ := ℓ) (qm := true) c L k
  have hq : ∀ u i, u < 256 → i < 8 → tauF S ℓ true c L k (qV u i) = (S (fx u i) && decide (ℓ (fx u i) < ℓ u)) := by
    intro u i hu hi; rw [tauF_lo (by unfold qV cbase; omega)]; exact t_q hu hi
  unfold cnfTrue cubeCnfQ
  rw [List.all_eq_true]
  intro cl' hcl
  simp only [List.mem_append] at hcl
  rcases hcl with ((((h | h) | h) | h) | h) | h
  · exact fam_fix hd A hA cl' h
  · exact fam_deg hp hd cl' h
  · exact fam_lvlQ hp hd hq cl' h
  · exact fam_def hd cl' h
  · exact fam_c4 hp hd cl' h
  · exact fam_cnt hp hc hL hk hsub cl' h

theorem no_pit_of_unsatQ {c L A k : Nat} (hu : Unsat (cubeCnfQ c L A k)) (hc : 1 ≤ c) (hL : L ≤ 255)
    (hk : 1 ≤ k) {S : Nat → Bool} {ℓ : Nat → Nat} (hp : Pit c L 64 S ℓ)
    (hA : ∀ u, u < 64 → S u = A.testBit u) (hsub : ∀ q, ((subcubes.getD q []).filter S).length ≤ k) : False := by
  have := bridgeQ hp hc hL hk hA hsub
  rw [hu] at this; exact absurd this (by simp)

end Dim8Lift.Cube

#print axioms Dim8Lift.Cube.no_pit_of_unsatQ
