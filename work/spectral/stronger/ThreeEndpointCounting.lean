import FiniteEndpointCounting

namespace Snake9
open Finset Classical
noncomputable section

theorem three_endpoint_images_card {m : Nat} (p : Snake m)
    {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (I : Finset α) (J : Finset β) (K : Finset γ)
    (f : α → Vertex) (g : β → Vertex) (h : γ → Vertex)
    (hfi : Set.InjOn f I) (hgi : Set.InjOn g J) (hhi : Set.InjOn h K)
    (hfs : ∀i∈I,InPath p (f i) ∧ AtMostOneNeighbor p (f i))
    (hgs : ∀j∈J,InPath p (g j) ∧ AtMostOneNeighbor p (g j))
    (hhs : ∀k∈K,InPath p (h k) ∧ AtMostOneNeighbor p (h k))
    (hfg : ∀i∈I,∀j∈J,f i≠g j)
    (hfh : ∀i∈I,∀k∈K,f i≠h k)
    (hgh : ∀j∈J,∀k∈K,g j≠h k) : I.card+J.card+K.card≤2 := by
  have hs : I.image f∪J.image g∪K.image h⊆selectedEndpoints p := by
    intro v hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
        exact hfs i hi
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
        exact hgs j hj
    · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
      exact hhs k hk
  have hfgd : Disjoint (I.image f) (J.image g) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hv
    obtain ⟨j,hj,he'⟩ := Finset.mem_image.mp hw
    exact hfg i hi j hj (he.trans he'.symm)
  have hhd : Disjoint (I.image f∪J.image g) (K.image h) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨k,hk,he'⟩ := Finset.mem_image.mp hw
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hv
      exact hfh i hi k hk (he.trans he'.symm)
    · obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hv
      exact hgh j hj k hk (he.trans he'.symm)
  have hc := (Finset.card_le_card hs).trans (selectedEndpoints_card p)
  rw [Finset.card_union_of_disjoint hhd,Finset.card_union_of_disjoint hfgd,
    Finset.card_image_of_injOn hfi,Finset.card_image_of_injOn hgi,Finset.card_image_of_injOn hhi] at hc
  exact hc

#print axioms three_endpoint_images_card
end
end Snake9
