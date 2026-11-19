import CubeBridge4
/-! Bridge, part 5: register values, and the bridge theorem. -/
set_option linter.deprecated false
namespace Dim8Lift.Cube
open Dim8Lift.Cnf Snake9.LocalWindow

variable {S : Nat → Bool} {ℓ : Nat → Nat}

theorem lt_block {i j K N : Nat} (hK : 0 < K) (hi1 : 1 ≤ i) (hi : i ≤ N) (hj1 : 1 ≤ j) (hj : j ≤ K) :
    (i - 1) * K + (j - 1) < N * K := by
  have h1 : (i - 1) * K + K = i * K := by
    have : i = (i - 1) + 1 := by omega
    conv => rhs; rw [this]
    rw [Nat.succ_mul]
  have h2 : i * K ≤ N * K := Nat.mul_le_mul_right K hi
  omega

theorem sum_two : ∀ n, ((List.range n).map (fun _ => 2)).sum = 2 * n := by
  intro n; induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp; omega
theorem endLits_len : endLits.length = 512 := by
  simp [endLits, R256, List.length_flatMap, sum_two]
theorem unselLits_len : unselLits.length = 256 := by simp [unselLits, R256]
theorem subLits_len (q : Nat) : (subLits q).length ≤ 256 := by
  unfold subLits; rw [List.length_map]
  unfold subcubes; rw [List.getD_eq_getElem?_getD]
  cases e : (List.flatMap _ pairs8)[q]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    have hm := List.mem_of_getElem? e
    simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range] at hm
    obtain ⟨_, _, v, _, hv⟩ := hm
    split at hv
    · simp at hv
    · simp only [Option.some.injEq] at hv; subst hv
      exact Nat.le_trans (List.length_filter_le _ _) (by simp [R256])

theorem hR_end {c L k : Nat} (hc : 1 ≤ c) : ∀ i j, 1 ≤ i → i ≤ endLits.length → 1 ≤ j → j ≤ 2 * c →
    tauF S ℓ c L k (reg cbase (2 * c) i j) = decide (j ≤ cl (tauF S ℓ c L k) endLits i) := by
  intro i j hi1 hi hj1 hj
  rw [endLits_len] at hi
  have hb := lt_block (K := 2 * c) (N := 512) (by omega) hi1 hi hj1 hj
  have hd := regdec i j (2 * c) (by omega) hj1 hj
  rw [cl_lo endLits (fun l hl => (endLits_lt l hl).1)]
  unfold tauF reg
  rw [if_neg (by omega), if_pos (by unfold b1; omega), show cbase + (i - 1) * (2 * c) + (j - 1) - cbase =
    (i - 1) * (2 * c) + (j - 1) by omega, hd.1, hd.2, show j - 1 + 1 = j by omega, show i - 1 + 1 = i by omega]

theorem hR_unsel {c L k : Nat} (hL : L ≤ 255) : ∀ i j, 1 ≤ i → i ≤ unselLits.length → 1 ≤ j → j ≤ 256 - L →
    tauF S ℓ c L k (reg (b1 c) (256 - L) i j) = decide (j ≤ cl (tauF S ℓ c L k) unselLits i) := by
  intro i j hi1 hi hj1 hj
  rw [unselLits_len] at hi
  have hb := lt_block (K := 256 - L) (N := 256) (by omega) hi1 hi hj1 hj
  have hd := regdec i j (256 - L) (by omega) hj1 hj
  rw [cl_lo unselLits (fun l hl => (unselLits_lt l hl).1)]
  unfold tauF reg
  rw [if_neg (by unfold b1; omega), if_neg (by omega), if_pos (by unfold b2; omega),
    show b1 c + (i - 1) * (256 - L) + (j - 1) - b1 c = (i - 1) * (256 - L) + (j - 1) by omega,
    hd.1, hd.2, show j - 1 + 1 = j by omega, show i - 1 + 1 = i by omega]

theorem hR_sub {c L k : Nat} (hk : 1 ≤ k) (q : Nat) : ∀ i j, 1 ≤ i → i ≤ (subLits q).length → 1 ≤ j → j ≤ k →
    tauF S ℓ c L k (reg (b2 c L + q * 256 * k) k i j) = decide (j ≤ cl (tauF S ℓ c L k) (subLits q) i) := by
  intro i j hi1 hi hj1 hj
  have hi' := Nat.le_trans hi (subLits_len q)
  have hb := lt_block (K := k) (N := 256) (by omega) hi1 hi' hj1 hj
  have hd := regdec i j k (by omega) hj1 hj
  have hq := decomp ((i - 1) * k + (j - 1)) q (256 * k) (by omega) (by rw [Nat.mul_comm 256 k]; omega)
  rw [cl_lo (subLits q) (fun l hl => (subLits_lt q l hl).1)]
  unfold tauF reg
  have e : b2 c L + q * 256 * k + (i - 1) * k + (j - 1) - b2 c L = (i - 1) * k + (j - 1) + q * (256 * k) := by
    rw [Nat.mul_assoc]; omega
  rw [if_neg (by unfold b2 b1; omega), if_neg (by unfold b2 b1; omega), if_neg (by unfold b2; omega), e,
    hq.1, hq.2, hd.1, hd.2, show j - 1 + 1 = j by omega, show i - 1 + 1 = i by omega]

theorem fam_cnt {c L k : Nat} (hp : Pit c L 64 S ℓ) (hc : 1 ≤ c) (hL : L ≤ 255) (hk : 1 ≤ k)
    (hsub : ∀ q, ((subcubes.getD q []).filter S).length ≤ k) :
    ∀ cl' ∈ famCnt c L k, clauseTrue (tauF S ℓ c L k) cl' = true := by
  intro cl' hcl
  unfold famCnt at hcl
  simp only [List.mem_append, List.mem_flatMap, List.mem_range] at hcl
  rcases hcl with (h | h) | ⟨q, _, h⟩
  · refine atMost_sound _ cbase (2 * c) endLits (by omega) (by unfold cbase; omega)
      (fun l hl => (endLits_lt l hl).2) (hR_end hc) ?_ _ h
    rw [cl_lo endLits (fun l hl => (endLits_lt l hl).1), cl_full, ends_count]; have := hp.ends; omega
  · refine atMost_sound _ (b1 c) (256 - L) unselLits (by omega) (by unfold b1 cbase; omega)
      (fun l hl => (unselLits_lt l hl).2) (hR_unsel hL) ?_ _ h
    rw [cl_lo unselLits (fun l hl => (unselLits_lt l hl).1), cl_full]
    have := unsel_count (S := S) (ℓ := ℓ); have := hp.card; omega
  · refine atMost_sound _ (b2 c L + q * 256 * k) k (subLits q) hk (by unfold b2 b1 cbase; omega)
      (fun l hl => (subLits_lt q l hl).2) (hR_sub hk q) ?_ _ h
    rw [cl_lo (subLits q) (fun l hl => (subLits_lt q l hl).1), cl_full, sub_count]; exact hsub q

/-- **Bridge.** A `Pit` with copy 0 equal to `A` and every other 6-subcube holding at most `k`
vertices satisfies the cube CNF. -/
theorem bridge {c L A k : Nat} (hp : Pit c L 64 S ℓ) (hc : 1 ≤ c) (hL : L ≤ 255) (hk : 1 ≤ k)
    (hA : ∀ u, u < 64 → S u = A.testBit u) (hsub : ∀ q, ((subcubes.getD q []).filter S).length ≤ k) :
    cnfTrue (tauF S ℓ c L k) (cubeCnfC4 c L A k) = true := by
  have hd := dec_tauF (S := S) (ℓ := ℓ) c L k
  unfold cnfTrue cubeCnfC4
  rw [List.all_eq_true]
  intro cl' hcl
  simp only [List.mem_append] at hcl
  rcases hcl with ((((h | h) | h) | h) | h) | h
  · exact fam_fix hd A hA cl' h
  · exact fam_deg hp hd cl' h
  · exact fam_lvl hp hd cl' h
  · exact fam_def hd cl' h
  · exact fam_c4 hp hd cl' h
  · exact fam_cnt hp hc hL hk hsub cl' h

theorem no_pit_of_unsat {c L A k : Nat} (hu : Unsat (cubeCnfC4 c L A k)) (hc : 1 ≤ c) (hL : L ≤ 255)
    (hk : 1 ≤ k) {S : Nat → Bool} {ℓ : Nat → Nat} (hp : Pit c L 64 S ℓ)
    (hA : ∀ u, u < 64 → S u = A.testBit u) (hsub : ∀ q, ((subcubes.getD q []).filter S).length ≤ k) : False := by
  have := bridge hp hc hL hk hA hsub
  rw [hu] at this; exact absurd this (by simp)

end Dim8Lift.Cube

#print axioms Dim8Lift.Cube.no_pit_of_unsat
