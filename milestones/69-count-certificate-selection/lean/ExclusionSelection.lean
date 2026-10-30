import Mathlib.Tactic

namespace Snake9.ExclusionSelection69
open Finset

def Covers {K : Type*} [DecidableEq K] (clauses : Finset (Finset K))
    (selected : Finset K) : Prop :=
  ∀ c ∈ clauses, ∃ k ∈ c, k ∈ selected

/-- A singleton clause forces its unique key into every covering selection. -/
theorem singleton_forces {K : Type*} [DecidableEq K]
    {clauses : Finset (Finset K)} {selected : Finset K} {k : K}
    (h : Covers clauses selected) (hk : {k} ∈ clauses) : k ∈ selected := by
  obtain ⟨j,hj,hs⟩ := h {k} hk
  have he : j=k := Finset.mem_singleton.mp hj
  simpa [he] using hs

/-- If the mandatory keys cover everything, they are the unique least cover. -/
theorem least_cover {K : Type*} [DecidableEq K]
    (clauses : Finset (Finset K)) (mandatory : Finset K)
    (hcover : Covers clauses mandatory)
    (hsingle : ∀ k ∈ mandatory, {k} ∈ clauses) :
    Covers clauses mandatory ∧
      ∀ selected, Covers clauses selected → mandatory ⊆ selected := by
  refine ⟨hcover,?_⟩
  intro selected h k hk
  exact singleton_forces h (hsingle k hk)

theorem minimum_cardinality {K : Type*} [DecidableEq K]
    (clauses : Finset (Finset K)) (mandatory selected : Finset K)
    (hsingle : ∀ k ∈ mandatory, {k} ∈ clauses)
    (h : Covers clauses selected) : mandatory.card ≤ selected.card := by
  apply Finset.card_le_card
  intro k hk
  exact singleton_forces h (hsingle k hk)

/-- An actual transition avoiding all selected exclusions satisfies the potential
    inequality if every negative transition contains one selected exclusion. -/
theorem potential_from_exclusions {E K : Type*} [DecidableEq K]
    (selected : Finset K) (occurs : K → E → Prop) (slack : E → ℤ)
    (hnegative : ∀ e, slack e < 0 → ∃ k ∈ selected, occurs k e)
    (e : E) (hvalid : ∀ k ∈ selected, ¬ occurs k e) : 0 ≤ slack e := by
  by_contra h
  obtain ⟨k,hk,he⟩ := hnegative e (by omega)
  exact hvalid k hk he

#print axioms singleton_forces
#print axioms least_cover
#print axioms minimum_cardinality
#print axioms potential_from_exclusions
end Snake9.ExclusionSelection69
