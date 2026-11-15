import Std

set_option Elab.async false

namespace Degree219

/-- Exact integer encoding of the degree equation at a selected vertex.
The available degree d and all subtractions are interpreted in Int. -/
theorem selected_degree_iff (x e s d : Int)
    (hx : x = 0 ∨ x = 1) (he : e = 0 ∨ e = 1)
    (hex : e ≤ x) (hs : 0 ≤ s) (hsd : s ≤ d) :
    (x = 1 → s = 2 - e) ↔
      (2 * x - e ≤ s ∧ s ≤ d - (d - 2) * x - e) := by
  rcases hx with rfl | rfl <;>
    rcases he with rfl | rfl <;>
    simp_all <;> omega

/-- Four linear inequalities encode the product of two Boolean selections.
No separate Boolean premise on the product variable is needed. -/
theorem edge_product_iff (x z y : Int)
    (hx : x = 0 ∨ x = 1) (hz : z = 0 ∨ z = 1) :
    y = x * z ↔ (0 ≤ y ∧ y ≤ x ∧ y ≤ z ∧ x + z - 1 ≤ y) := by
  rcases hx with rfl | rfl <;>
    rcases hz with rfl | rfl <;>
    simp_all <;> omega

/-- A signed residual coefficient is bounded using only an integer variable's
box constraints. Negative coefficients contribute no positive allowance. -/
theorem residual_term_le (r v : Int) (hzero : 0 ≤ v) (hone : v ≤ 1) :
    r * v ≤ max r 0 := by
  have hv : v = 0 ∨ v = 1 := by omega
  rcases hv with rfl | rfl
  · simpa using Int.le_max_right r 0
  · simpa using Int.le_max_left r 0

private theorem sum_map_le {α : Type} (indices : List α) (f g : α → Int)
    (h : ∀ i, i ∈ indices → f i ≤ g i) :
    (indices.map f).sum ≤ (indices.map g).sum := by
  induction indices with
  | nil => simp
  | cons a tail ih =>
      have first := h a (by simp)
      have rest := ih (by
        intro i hi
        exact h i (by simp [hi]))
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Exact weighted-row certificate with residual compensation.
The algebraic identity must be proved from the actual coefficient arrays;
it is an equality premise, not an assumed objective inequality. All row
inequalities and nonnegative inequality multipliers remain explicit. -/
theorem residual_certificate_bound {ι κ τ : Type}
    (variables : List ι) (inequalities : List κ) (equalities : List τ)
    (value residual : ι → Int)
    (Y left bound : κ → Int) (Z eqleft eqbound : τ → Int)
    (scale objective : Int)
    (hvalue : ∀ j, j ∈ variables → 0 ≤ value j ∧ value j ≤ 1)
    (hY : ∀ i, i ∈ inequalities → 0 ≤ Y i)
    (hrows : ∀ i, i ∈ inequalities → left i ≤ bound i)
    (hequalities : ∀ i, i ∈ equalities → eqleft i = eqbound i)
    (identity : scale * objective =
      (inequalities.map (fun i => Y i * left i)).sum +
      (equalities.map (fun i => Z i * eqleft i)).sum +
      (variables.map (fun j => residual j * value j)).sum) :
    scale * objective ≤
      (inequalities.map (fun i => Y i * bound i)).sum +
      (equalities.map (fun i => Z i * eqbound i)).sum +
      (variables.map (fun j => max (residual j) 0)).sum := by
  have hineq := sum_map_le inequalities
    (fun i => Y i * left i) (fun i => Y i * bound i) (by
      intro i hi
      exact Int.mul_le_mul_of_nonneg_left (hrows i hi) (hY i hi))
  have heq := sum_map_le equalities
    (fun i => Z i * eqleft i) (fun i => Z i * eqbound i) (by
      intro i hi
      change Z i * eqleft i ≤ Z i * eqbound i
      rw [hequalities i hi]
      exact Int.le_refl _)
  have hres := sum_map_le variables
    (fun j => residual j * value j) (fun j => max (residual j) 0) (by
      intro j hj
      exact residual_term_le (residual j) (value j) (hvalue j hj).1 (hvalue j hj).2)
  omega

#print axioms selected_degree_iff
#print axioms edge_product_iff
#print axioms residual_term_le
#print axioms residual_certificate_bound
end Degree219
