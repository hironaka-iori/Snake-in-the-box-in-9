import Mathlib.Tactic

namespace Snake9.BonusCriterion86

theorem finite_minimum_exists {C : Type*} [Finite C] [Nonempty C] (f : C → ℚ) :
    ∃ c, ∀ d, f c ≤ f d := Finite.exists_min f

theorem mean_non_decreasing {C : Type*} (base bonus : C → ℚ) (μ ν : ℚ)
    (hlower : ∀ c, μ ≤ base c) (hb : ∀ c, 0 ≤ bonus c)
    (hattains : ∃ c, base c + bonus c = ν) : μ ≤ ν := by
  obtain ⟨c,hc⟩ := hattains
  have h0 := hlower c
  have h1 := hb c
  linarith

theorem equality_iff_unaffected_critical {C : Type*} (base bonus : C → ℚ) (μ ν : ℚ)
    (hlower : ∀ c, μ ≤ base c) (hb : ∀ c, 0 ≤ bonus c)
    (hnewlower : ∀ c, ν ≤ base c + bonus c)
    (hattains : ∃ c, base c + bonus c = ν) :
    ν = μ ↔ ∃ c, base c = μ ∧ bonus c = 0 := by
  constructor
  · intro heq
    obtain ⟨c,hc⟩ := hattains
    have h0 := hlower c
    have h1 := hb c
    refine ⟨c, ?_, ?_⟩ <;> linarith
  · rintro ⟨c,hc,hzero⟩
    have hmin := mean_non_decreasing base bonus μ ν hlower hb hattains
    have hnew := hnewlower c
    linarith

theorem strict_iff_all_critical_affected {C : Type*} (base bonus : C → ℚ) (μ ν : ℚ)
    (hlower : ∀ c, μ ≤ base c) (hb : ∀ c, 0 ≤ bonus c)
    (hnewlower : ∀ c, ν ≤ base c + bonus c)
    (hattains : ∃ c, base c + bonus c = ν) :
    μ < ν ↔ ∀ c, base c = μ → 0 < bonus c := by
  have heq := equality_iff_unaffected_critical base bonus μ ν hlower hb hnewlower hattains
  have hmin := mean_non_decreasing base bonus μ ν hlower hb hattains
  constructor
  · intro hstrict c hc
    by_contra h
    have hzero : bonus c = 0 := le_antisymm (le_of_not_gt h) (hb c)
    have he := heq.mpr ⟨c,hc,hzero⟩
    linarith
  · intro h
    rcases lt_or_eq_of_le hmin with hlt | he
    · exact hlt
    · obtain ⟨c,hc,hzero⟩ := heq.mp he.symm
      have hp := h c hc
      linarith

theorem nonnegative_sum_zero_iff (n : Nat) (bonus : Fin n → ℚ)
    (hb : ∀ i, 0 ≤ bonus i) : (∑ i, bonus i) = 0 ↔ ∀ i, bonus i = 0 := by
  constructor
  · intro hs i
    have hi : bonus i ≤ ∑ j, bonus j :=
      Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i)
    have h0 := hb i
    linarith
  · intro h
    simp only [h, Finset.sum_const_zero]

theorem average_bonus_zero_iff (n : Nat) (bonus : Fin n → ℚ)
    (hb : ∀ i, 0 ≤ bonus i) (length : ℚ) (hl : 0 < length) :
    (∑ i, bonus i) / length = 0 ↔ ∀ i, bonus i = 0 := by
  rw [div_eq_zero_iff]
  simp only [ne_of_gt hl, or_false]
  exact nonnegative_sum_zero_iff n bonus hb

theorem average_bonus_nonnegative (n : Nat) (bonus : Fin n → ℚ)
    (hb : ∀ i, 0 ≤ bonus i) (length : ℚ) (hl : 0 < length) :
    0 ≤ (∑ i, bonus i) / length :=
  div_nonneg (Finset.sum_nonneg (fun i _ => hb i)) (le_of_lt hl)

#print axioms finite_minimum_exists
#print axioms mean_non_decreasing
#print axioms equality_iff_unaffected_critical
#print axioms strict_iff_all_critical_affected
#print axioms nonnegative_sum_zero_iff
#print axioms average_bonus_zero_iff
#print axioms average_bonus_nonnegative
end Snake9.BonusCriterion86
