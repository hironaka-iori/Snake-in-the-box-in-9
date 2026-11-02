import Mathlib.Tactic

/-!
Rational potential comparison for a fixed weighted directed graph.

The graph is represented here only by the supplied per-step inequalities.
Concrete edge membership, weight interpretation, local-share premises and the
complete potential certificate are separate obligations. This source is written
for later checking; its presence does not assert successful compilation.
-/

namespace Snake9.PotentialComparison93

/-- Telescope along an open walk. Weights and potentials use the same rational
scale as the slope. No closed-walk or nonnegativity assumption is required. -/
theorem path_telescope (mu : ℚ) (pi : Nat → ℚ) (f : Nat → Nat)
    (w : Nat → ℚ) : ∀ n : Nat,
    (∀ i < n, mu + pi (f (i+1)) ≤ w i + pi (f i)) →
    (n : ℚ) * mu + pi (f n) ≤
      (∑ i ∈ Finset.range n, w i) + pi (f 0) := by
  intro n
  induction n with
  | zero =>
      intro _
      simp
  | succ n ih =>
      intro hstep
      have hprev := ih (by
        intro i hi
        exact hstep i (Nat.lt_trans hi (Nat.lt_succ_self n)))
      have hlast := hstep n (Nat.lt_succ_self n)
      simp only [Finset.sum_range_succ, Nat.cast_succ]
      nlinarith

/-- A path deficit is a lower bound for any bound on the potential drop
between its endpoints. A global potential range supplies such a bound. -/
theorem path_deficit_le_range (mu rho : ℚ) (pi : Nat → ℚ)
    (f : Nat → Nat) (w : Nat → ℚ) (n : Nat)
    (hstep : ∀ i < n, mu + pi (f (i+1)) ≤ w i + pi (f i))
    (hspan : pi (f 0) ≤ pi (f n) + rho) :
    (n : ℚ) * mu - (∑ i ∈ Finset.range n, w i) ≤ rho := by
  have h := path_telescope mu pi f w n hstep
  linarith

/-- A nonempty closed walk of mean M caps every feasible competing slope. -/
theorem cycle_mean_caps_slope (mu M : ℚ) (pi : Nat → ℚ)
    (f : Nat → Nat) (w : Nat → ℚ) (n : Nat) (hn : 0 < n)
    (hstep : ∀ i < n, mu + pi (f (i+1)) ≤ w i + pi (f i))
    (hclosed : f n = f 0)
    (hsum : (∑ i ∈ Finset.range n, w i) = (n : ℚ) * M) :
    mu ≤ M := by
  have h := path_telescope mu pi f w n hstep
  rw [hclosed, hsum] at h
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hmul : (n : ℚ) * mu ≤ (n : ℚ) * M := by linarith
  exact (mul_le_mul_left hnq).mp hmul

/-- A short tight path and a slope ceiling certify the best comparison value
for the fixed budget constants 1098960, 4200 and 8.

The baseline value is supplied through a cross-multiplied identity. To identify
it with its quotient, separately require 0 < 4200 + M. Only the competing
denominator needs positivity for this implication itself. -/
theorem comparison_of_slope_and_range
    (M R k C Bstar mu rho : ℚ)
    (hbase : 1098960 + 8*M + R = Bstar*(4200+M))
    (htight : R = k*M-C)
    (hslope : mu ≤ M)
    (hpath : k*mu-C ≤ rho)
    (hlength : k+8 ≤ Bstar)
    (hden : 0 < 4200+mu) :
    Bstar ≤ (1098960+8*mu+rho)/(4200+mu) := by
  apply (le_div_iff₀ hden).2
  have hproduct : 0 ≤ (k+8-Bstar)*(mu-M) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  nlinarith

/-- Conditional comparison for mean 483: the proposed nine-edge witness has
total weight 3796 and deficit 551. No edge membership is asserted here. -/
theorem completed_483_comparison (mu rho : ℚ)
    (hslope : mu ≤ 483)
    (hpath : 9*mu-3796 ≤ rho)
    (hden : 0 < 4200+mu) :
    (157625 : ℚ)/669 ≤ (1098960+8*mu+rho)/(4200+mu) := by
  exact comparison_of_slope_and_range
    483 551 9 3796 (157625/669) mu rho
    (by norm_num) (by norm_num) hslope hpath (by norm_num) hden

/-- Conditional comparison for mean 9259/19. The range is 11301/19 in
unscaled weight units; the 31-edge witness has total weight 14512. -/
theorem additional_9259_19_comparison (mu rho : ℚ)
    (hslope : mu ≤ (9259 : ℚ)/19)
    (hpath : 31*mu-14512 ≤ rho)
    (hden : 0 < 4200+mu) :
    (20965613 : ℚ)/89059 ≤ (1098960+8*mu+rho)/(4200+mu) := by
  exact comparison_of_slope_and_range
    (9259/19) (11301/19) 31 14512 (20965613/89059) mu rho
    (by norm_num) (by norm_num) hslope hpath (by norm_num) hden

/-- Conditional comparison for mean 496: the proposed seven-edge witness has
total weight 2872 and deficit 600. The local-share assumptions are separate. -/
theorem full_496_comparison (mu rho : ℚ)
    (hslope : mu ≤ 496)
    (hpath : 7*mu-2872 ≤ rho)
    (hden : 0 < 4200+mu) :
    (137941 : ℚ)/587 ≤ (1098960+8*mu+rho)/(4200+mu) := by
  exact comparison_of_slope_and_range
    496 600 7 2872 (137941/587) mu rho
    (by norm_num) (by norm_num) hslope hpath (by norm_num) hden

#print axioms path_telescope
#print axioms path_deficit_le_range
#print axioms cycle_mean_caps_slope
#print axioms comparison_of_slope_and_range
#print axioms completed_483_comparison
#print axioms additional_9259_19_comparison
#print axioms full_496_comparison

end Snake9.PotentialComparison93
