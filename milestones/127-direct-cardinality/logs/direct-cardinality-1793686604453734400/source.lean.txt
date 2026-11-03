import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-!
Direct clauses for a positive lower cardinality bound. Positions, rather than
the values stored at those positions, are counted; repeated values are allowed.
This module supplies generic counting semantics, not a snake exclusion or a
proof that a concrete clause is derivable by reverse unit propagation.
-/
namespace Snake9.DirectCardinality127
open Finset

theorem lower_bound_iff_direct_clauses {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (absent : ι → Prop) [DecidablePred absent]
    (k : Nat) (hk0 : 0 < k) (hks : k ≤ s.card+1) :
    k ≤ (s.filter absent).card ↔
      ∀ omitted : Finset ι, omitted ⊆ s → omitted.card = k-1 →
        ∃ i ∈ s, i ∉ omitted ∧ absent i := by
  constructor
  · intro h omitted _ hcard
    by_contra hn
    have hsub : s.filter absent ⊆ omitted := by
      intro i hi
      obtain ⟨his, ha⟩ := Finset.mem_filter.mp hi
      by_contra hio
      exact hn ⟨i, his, hio, ha⟩
    have hc := Finset.card_le_card hsub
    omega
  · intro h
    by_contra hn
    have hc : (s.filter absent).card ≤ k-1 := by omega
    have hsub : s.filter absent ⊆ s := by
      intro i hi
      exact (Finset.mem_filter.mp hi).1
    obtain ⟨omitted, hlo, hhi, hcard⟩ :=
      Finset.exists_subsuperset_card_eq hsub hc (by omega : k-1 ≤ s.card)
    obtain ⟨i, his, hio, ha⟩ := h omitted hhi hcard
    exact hio (hlo (Finset.mem_filter.mpr ⟨his, ha⟩))

theorem lower_bound_iff_complement_upper {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (absent : ι → Prop) [DecidablePred absent]
    (k : Nat) (hk : k ≤ s.card) :
    k ≤ (s.filter absent).card ↔
      (s.filter fun i => ¬ absent i).card ≤ s.card-k := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := s) absent
  omega

-- No injectivity condition is imposed on corner. Repeated corner values
-- remain distinct positions and retain their multiplicity in the lower bound.
theorem absent_positions_iff_direct_clauses {V : Type*}
    (n k : Nat) (corner : Fin n → V) (selected : V → Bool)
    (hk0 : 0 < k) (hkn : k ≤ n+1) :
    k ≤ ((Finset.univ : Finset (Fin n)).filter
      (fun i => selected (corner i) = false)).card ↔
      ∀ omitted : Finset (Fin n), omitted.card = k-1 →
        ∃ i, i ∉ omitted ∧ selected (corner i) = false := by
  have h := lower_bound_iff_direct_clauses (Finset.univ : Finset (Fin n))
    (fun i => selected (corner i) = false) k hk0 (by simpa using hkn)
  constructor
  · intro hc omitted hcard
    obtain ⟨i, _, hi, ha⟩ := h.mp hc omitted (Finset.subset_univ _) hcard
    exact ⟨i, hi, ha⟩
  · intro hc
    apply h.mpr
    intro omitted _ hcard
    obtain ⟨i, hi, ha⟩ := hc omitted hcard
    exact ⟨i, Finset.mem_univ _, hi, ha⟩

theorem number_of_omission_sets (n k : Nat) :
    ((Finset.univ : Finset (Fin n)).powersetCard (k-1)).card =
      Nat.choose n (k-1) := by simp

theorem clause_counts_for_six_centres :
    Nat.choose 21 0 = 1 ∧ Nat.choose 21 1 = 21 ∧ Nat.choose 21 2 = 210 ∧
      4 * Nat.choose 21 0 + Nat.choose 21 1 + Nat.choose 21 2 = 235 := by
  decide

#print axioms lower_bound_iff_direct_clauses
#print axioms lower_bound_iff_complement_upper
#print axioms absent_positions_iff_direct_clauses
#print axioms number_of_omission_sets
#print axioms clause_counts_for_six_centres
end Snake9.DirectCardinality127
