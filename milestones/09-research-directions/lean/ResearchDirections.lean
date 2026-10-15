import Mathlib.Tactic

namespace SnakeResearchDirections

/-- A 192-vertex example with 1632 singleton squares limits any uniform density coefficient. -/
theorem uniform_density_cap (c : ℚ) (h : c * 192 ≤ 1632) : c ≤ 17 / 2 := by
  linarith

/-- The square census equations and even the largest allowed coefficient
still admit a numerical census with 211 vertices. No snake realizing this
census is asserted. The 1632-count witness premise is audited separately. -/
theorem density_only_census_feasible (c : ℚ) (hc : c ≤ 17 / 2) :
    (17 + 1795 + 2587 + 209 = (4608 : Nat)) ∧
    (1795 + 2 * 2587 + 3 * 209 = 36 * (211 : Nat)) ∧
    (209 + 2 = (211 : Nat)) ∧
    c * 211 ≤ 1795 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  linarith

/-- Fractional endpoint accounting, with integer weights and a common denominator.
Every demand contains an endpoint. Each endpoint can carry at most D units
of weight, so all demands together carry at most r*D units. -/
theorem endpoint_weight_budget (n r D : Nat) (w : Fin n → Nat)
    (contains : Fin n → Fin r → Prop) [DecidableRel contains]
    (nonempty : ∀ i, ∃ e, contains i e)
    (capacity : ∀ e, (∑ i : Fin n, if contains i e then w i else 0) ≤ D) :
    (∑ i : Fin n, w i) ≤ r * D := by
  have hi (i : Fin n) : w i ≤ ∑ e : Fin r, if contains i e then w i else 0 := by
    obtain ⟨e, he⟩ := nonempty i
    calc
      w i = (if contains i e then w i else 0) := by simp [he]
      _ ≤ ∑ e : Fin r, if contains i e then w i else 0 :=
        Finset.single_le_sum (f := fun e : Fin r => if contains i e then w i else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
  calc
    (∑ i : Fin n, w i) ≤ ∑ i : Fin n, ∑ e : Fin r, if contains i e then w i else 0 :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = ∑ e : Fin r, ∑ i : Fin n, if contains i e then w i else 0 := Finset.sum_comm
    _ ≤ ∑ _e : Fin r, D := Finset.sum_le_sum (fun e _ => capacity e)
    _ = r * D := by simp

/-- Five cyclic pair demands cannot be met by only two endpoint indicators. -/
theorem five_cycle_endpoint_demands :
    ∀ a b c d e : Bool,
    (a = true ∨ b = true) → (b = true ∨ c = true) →
    (c = true ∨ d = true) → (d = true ∨ e = true) →
    (e = true ∨ a = true) →
    ¬ ([a,b,c,d,e].count true ≤ 2) := by
  intro a b c d e
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

#print axioms five_cycle_endpoint_demands
#print axioms uniform_density_cap
#print axioms density_only_census_feasible
#print axioms endpoint_weight_budget
end SnakeResearchDirections
