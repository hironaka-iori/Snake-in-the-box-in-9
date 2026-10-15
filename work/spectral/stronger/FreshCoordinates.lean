import CubeLocal
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace Snake9

theorem exists_four_coords_outside_five (a b i c d : Coord) :
    ∃ j : Fin 4 → Coord,
      (∀ k, j k ≠ a ∧ j k ≠ b ∧ j k ≠ i ∧ j k ≠ c ∧ j k ≠ d) ∧
      Function.Injective j := by
  classical
  let forbidden : Finset Coord := {a,b,i,c,d}
  let allowed := Finset.univ \ forbidden
  have hsmall : forbidden.card ≤ 5 := Finset.card_le_five
  have hcard : allowed.card = 9 - forbidden.card := by
    simp [allowed, Finset.card_sdiff (Finset.subset_univ forbidden), Coord]
  have hlarge : Fintype.card (Fin 4) ≤ allowed.card := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨j,hj⟩ := Function.Embedding.exists_of_card_le_finset hlarge
  refine ⟨j, ?_, j.injective⟩
  intro k
  have hm : j k ∈ allowed := hj ⟨k,rfl⟩
  simpa only [allowed, forbidden, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton, not_or] using hm

theorem exists_five_coords_outside_four (a b c d : Coord) :
    ∃ j : Fin 5 → Coord,
      (∀ k, j k ≠ a ∧ j k ≠ b ∧ j k ≠ c ∧ j k ≠ d) ∧
      Function.Injective j := by
  classical
  let forbidden : Finset Coord := {a,b,c,d}
  let allowed := Finset.univ \ forbidden
  have hsmall : forbidden.card ≤ 4 := Finset.card_le_four
  have hcard : allowed.card = 9 - forbidden.card := by
    simp [allowed, Finset.card_sdiff (Finset.subset_univ forbidden), Coord]
  have hlarge : Fintype.card (Fin 5) ≤ allowed.card := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨j,hj⟩ := Function.Embedding.exists_of_card_le_finset hlarge
  refine ⟨j, ?_, j.injective⟩
  intro k
  have hm : j k ∈ allowed := hj ⟨k,rfl⟩
  simpa only [allowed, forbidden, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton, not_or] using hm

#print axioms exists_four_coords_outside_five
#print axioms exists_five_coords_outside_four
end Snake9
