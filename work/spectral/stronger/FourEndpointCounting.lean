import FiniteEndpointCounting

namespace Snake9
open Finset Classical
noncomputable section

theorem four_endpoint_finsets_card {m : Nat} (p : Snake m) (I J K L : Finset Vertex)
    (hI : ∀v∈I,InPath p v ∧ AtMostOneNeighbor p v)
    (hJ : ∀v∈J,InPath p v ∧ AtMostOneNeighbor p v)
    (hK : ∀v∈K,InPath p v ∧ AtMostOneNeighbor p v)
    (hL : ∀v∈L,InPath p v ∧ AtMostOneNeighbor p v)
    (hIJ : Disjoint I J) (hIK : Disjoint I K) (hIL : Disjoint I L)
    (hJK : Disjoint J K) (hJL : Disjoint J L) (hKL : Disjoint K L) :
    I.card+J.card+K.card+L.card≤2 := by
  have hsub : I∪J∪K∪L⊆selectedEndpoints p := by
    intro v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_union.mp hv with hv | hv
        · exact hI v hv
        · exact hJ v hv
      · exact hK v hv
    · exact hL v hv
  have hIJK : Disjoint (I∪J) K := Finset.disjoint_union_left.mpr ⟨hIK,hJK⟩
  have hIJKL : Disjoint (I∪J∪K) L :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hIL,hJL⟩,hKL⟩
  have hb := (Finset.card_le_card hsub).trans (selectedEndpoints_card p)
  rwa [Finset.card_union_of_disjoint hIJKL,Finset.card_union_of_disjoint hIJK,
    Finset.card_union_of_disjoint hIJ] at hb

#print axioms four_endpoint_finsets_card
end
end Snake9
