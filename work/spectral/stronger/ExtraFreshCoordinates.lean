import FreshCoordinates

namespace Snake9
theorem exists_two_coords_outside_seven (a b c d e f g : Coord) :
    ∃ j : Fin 2 → Coord,
      (∀ k, j k≠a ∧ j k≠b ∧ j k≠c ∧ j k≠d ∧ j k≠e ∧ j k≠f ∧ j k≠g) ∧
      Function.Injective j := by
  classical
  let forbidden : Finset Coord := {a,b,c,d,e,f,g}
  let allowed := Finset.univ \ forbidden
  have hsmall : forbidden.card ≤ 7 := by
    have hx : ({c,d,e,f,g} : Finset Coord).card ≤ 5 := Finset.card_le_five
    have hy := Finset.card_insert_le b ({c,d,e,f,g} : Finset Coord)
    have hz := Finset.card_insert_le a ({b,c,d,e,f,g} : Finset Coord)
    dsimp [forbidden]
    omega
  have hcard : allowed.card = 9 - forbidden.card := by
    simp [allowed, Finset.card_sdiff (Finset.subset_univ forbidden), Coord]
  have hlarge : Fintype.card (Fin 2) ≤ allowed.card := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨j,hj⟩ := Function.Embedding.exists_of_card_le_finset hlarge
  refine ⟨j,?_,j.injective⟩
  intro k
  have hm : j k ∈ allowed := hj ⟨k,rfl⟩
  simpa only [allowed,forbidden,Finset.mem_sdiff,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton,not_or] using hm
#print axioms exists_two_coords_outside_seven
end Snake9
