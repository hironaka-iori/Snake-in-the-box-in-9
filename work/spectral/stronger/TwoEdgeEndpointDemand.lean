import StarOuterCounting

namespace Snake9
open Finset Classical
noncomputable section

/-- Two missing pairs on five ordinary coordinates demand at least three distinct resources. -/
theorem two_edge_endpoint_demand (R : Finset Coord) (F : Finset (Finset Coord))
    (hR : R.card=5) (hF : F.card=2) (hedge : ∀s∈F,s.card=2) :
    3≤(starIsolatedIndices R F).card+(starOrdinaryEdges R F).card := by
  obtain ⟨s,t,hst,hFst⟩ := Finset.card_eq_two.mp hF
  have hsF : s∈F := by rw [hFst]; simp
  have htF : t∈F := by rw [hFst]; simp
  have hs2 : (s∩R).card≤2 := (Finset.card_le_card Finset.inter_subset_left).trans_eq (hedge s hsF)
  have ht2 : (t∩R).card≤2 := (Finset.card_le_card Finset.inter_subset_left).trans_eq (hedge t htF)
  have hi : (starIsolatedIndices R F).card+(R∩F.biUnion id).card=5 := by
    exact (Finset.card_sdiff_add_card_inter R (F.biUnion id)).trans hR
  have hb := family_two_edge_inter_bound F s t R hFst
  by_cases hsR : s⊆R
  · by_cases htR : t⊆R
    · have hrr : (starOrdinaryEdges R F).card=2 := by simp [starOrdinaryEdges,hFst,Finset.filter_insert,Finset.filter_singleton,hsR,htR,hst]
      omega
    · have ht1 := two_edge_inter_card t R R (hedge t htF) (Finset.Subset.refl _) htR
      have hrr : (starOrdinaryEdges R F).card=1 := by simp [starOrdinaryEdges,hFst,Finset.filter_insert,Finset.filter_singleton,hsR,htR]
      omega
  · have hs1 := two_edge_inter_card s R R (hedge s hsF) (Finset.Subset.refl _) hsR
    by_cases htR : t⊆R
    · have hrr : (starOrdinaryEdges R F).card=1 := by simp [starOrdinaryEdges,hFst,Finset.filter_insert,Finset.filter_singleton,hsR,htR]
      omega
    · have ht1 := two_edge_inter_card t R R (hedge t htF) (Finset.Subset.refl _) htR
      have hrr : (starOrdinaryEdges R F).card=0 := by simp [starOrdinaryEdges,hFst,Finset.filter_insert,Finset.filter_singleton,hsR,htR]
      omega

#print axioms two_edge_endpoint_demand
end
end Snake9
