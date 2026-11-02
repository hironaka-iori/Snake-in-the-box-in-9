import Mathlib.Tactic

namespace Snake9.CreditPressure97

theorem floor_weight_monotone (base entering a b : Nat) (hab : a ≤ b) :
    max base (120*entering+a) ≤ max base (120*entering+b) :=
  max_le_max_left base (Nat.add_le_add_left hab _)

theorem potential_step_monotone {E V : Type} (source target : E → V)
    (w₁ w₂ : E → ℚ) (π : V → ℚ) (p : ℚ)
    (hweights : ∀ e, w₁ e ≤ w₂ e)
    (hstep : ∀ e, p+π (target e) ≤ w₁ e+π (source e)) :
    ∀ e, p+π (target e) ≤ w₂ e+π (source e) := by
  intro e
  exact (hstep e).trans (add_le_add_right (hweights e) _)

/-- Arithmetic only: the actual charge and potential inequalities must still
be supplied. The largest integer range allowed at slope496 is631. -/
theorem upper234_of_charge_and_potential (m W R : Nat)
    (hm : 9 ≤ m) (hcharge : W+4200*m ≤ 1098960)
    (hpotential : 496*(m-8) ≤ W+R) (hR : R ≤ 631) : m ≤ 234 := by
  omega

/-- Reuse the milestone74 cycle/path argument. Concrete membership, edge
weights and telescoping hypotheses remain separate evidence. -/
theorem path_deficit_obstruction (p R L W : ℚ)
    (hL : L ≤ 227) (hp : p ≤ 496)
    (hpath : p*L-W ≤ R) (hdeficit : 632 ≤ 496*L-W) :
    227*p-R ≤ 111960 := by
  have hmul := mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hp)
  nlinarith

/-- Abstract monotonic consequence of the saved finite-graph certificates.
The concrete graph inequalities and witness memberships remain separate. -/
theorem attainable_floor_vectors (works : (Fin 5 → Nat) → Prop)
    (hmono : Monotone works)
    (hgood : works ![16,18,16,16,16])
    (hbad0 : ¬ works ![15,20,16,16,16])
    (hbad1 : ¬ works ![16,17,16,16,16])
    (hbad2 : ¬ works ![16,20,15,16,16])
    (hbad3 : ¬ works ![16,20,16,15,16])
    (hbad4 : ¬ works ![16,20,16,16,15])
    (a : Fin 5 → Nat) (ha : a ≤ ![16,20,16,16,16]) :
    works a ↔ ![16,18,16,16,16] ≤ a := by
  constructor
  · intro hworks
    have h0 : 16 ≤ a 0 := by
      by_contra hn
      have hsmall : a 0 ≤ 15 := by omega
      apply hbad0
      apply (hmono ?_) hworks
      intro i
      fin_cases i
      · exact hsmall
      · exact ha 1
      · exact ha 2
      · exact ha 3
      · exact ha 4
    have h1 : 18 ≤ a 1 := by
      by_contra hn
      have hsmall : a 1 ≤ 17 := by omega
      apply hbad1
      apply (hmono ?_) hworks
      intro i
      fin_cases i
      · exact ha 0
      · exact hsmall
      · exact ha 2
      · exact ha 3
      · exact ha 4
    have h2 : 16 ≤ a 2 := by
      by_contra hn
      have hsmall : a 2 ≤ 15 := by omega
      apply hbad2
      apply (hmono ?_) hworks
      intro i
      fin_cases i
      · exact ha 0
      · exact ha 1
      · exact hsmall
      · exact ha 3
      · exact ha 4
    have h3 : 16 ≤ a 3 := by
      by_contra hn
      have hsmall : a 3 ≤ 15 := by omega
      apply hbad3
      apply (hmono ?_) hworks
      intro i
      fin_cases i
      · exact ha 0
      · exact ha 1
      · exact ha 2
      · exact hsmall
      · exact ha 4
    have h4 : 16 ≤ a 4 := by
      by_contra hn
      have hsmall : a 4 ≤ 15 := by omega
      apply hbad4
      apply (hmono ?_) hworks
      intro i
      fin_cases i
      · exact ha 0
      · exact ha 1
      · exact ha 2
      · exact ha 3
      · exact hsmall
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · intro hlower
    exact (hmono hlower) hgood

#print axioms upper234_of_charge_and_potential
#print axioms path_deficit_obstruction
#print axioms attainable_floor_vectors
#print axioms floor_weight_monotone
#print axioms potential_step_monotone

end Snake9.CreditPressure97
