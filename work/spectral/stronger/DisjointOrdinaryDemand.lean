import DisjointOneOrdinaryCount
import OrdinaryTwoEdgeDemand

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

theorem disjoint_ordinary_endpoint_demand (F : Finset (Finset Coord)) (R A B : Finset Coord)
    (c d : Coord) (hR : R.card=5) (hF : F.card=2) (hedge : ∀s∈F,s.card=2)
    (hA : A.card=2) (hB : B.card=2) (hAR : A⊆R) (hBR : B⊆R)
    (hAB : Disjoint A B) (hc : c∉R) (hd : d∉R) (hcd : c≠d) :
    3≤ordinaryEndpointDemand F R A B c d := by
  rcases disjoint_good_rows_or_three F R A B c d hR hF hA hB hAB hc hd hcd with hall | hthree
  swap
  · dsimp [ordinaryEndpointDemand]
    omega
  have hI : (starIsolatedIndices R F).card≤(ordinaryGoodIndices F R A B c d).card := by
    apply Finset.card_le_card
    intro k hk
    obtain ⟨hkR,hkn⟩ := Finset.mem_sdiff.mp hk
    exact Finset.mem_filter.mpr ⟨hkR,hall k hkR (fun s hs hks => hkn (Finset.mem_biUnion.mpr ⟨s,hs,hks⟩))⟩
  obtain ⟨s,t,hst,hFst⟩ := Finset.card_eq_two.mp hF
  have hsF : s∈F := by rw [hFst]; simp
  have htF : t∈F := by rw [hFst]; simp
  by_cases hsR : s⊆R
  · by_cases htR : t⊆R
    · have hsub : ∀u∈F,u⊆R := by
        intro u hu
        rw [hFst] at hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact hsR
        · exact Finset.mem_singleton.mp hu ▸ htR
      have hb := ordinary_two_edge_demand R A B F c d hR hA hB hF hedge hsub hAB hc hd
      have heA : F.filter (fun u => u⊆R ∧ Disjoint u A)=F.filter (fun u => Disjoint u A) := by
        ext u; simp only [Finset.mem_filter]; exact ⟨fun hu => ⟨hu.1,hu.2.2⟩,fun hu => ⟨hu.1,hsub u hu.1,hu.2⟩⟩
      have heB : F.filter (fun u => u⊆R ∧ Disjoint u B)=F.filter (fun u => Disjoint u B) := by
        ext u; simp only [Finset.mem_filter]; exact ⟨fun hu => ⟨hu.1,hu.2.2⟩,fun hu => ⟨hu.1,hsub u hu.1,hu.2⟩⟩
      dsimp [ordinaryEndpointDemand]
      rw [heA,heB]
      omega
    · have hb := disjoint_one_ordinary_demand F R A B s t c d hR hFst (hedge s hsF) (hedge t htF)
        hsR htR hA hB hAR hBR hAB hc hd
      dsimp [ordinaryEndpointDemand]
      omega
  · by_cases htR : t⊆R
    · have hb := disjoint_one_ordinary_demand F R A B t s c d hR (by rw [hFst]; exact Finset.pair_comm _ _)
        (hedge t htF) (hedge s hsF) htR hsR hA hB hAR hBR hAB hc hd
      dsimp [ordinaryEndpointDemand]
      omega
    · have hs1 := two_edge_inter_card s R R (hedge s hsF) (Finset.Subset.refl _) hsR
      have ht1 := two_edge_inter_card t R R (hedge t htF) (Finset.Subset.refl _) htR
      have hb := family_two_edge_inter_bound F s t R hFst
      have hi := Finset.card_sdiff_add_card_inter R (F.biUnion id)
      change (starIsolatedIndices R F).card+(R∩F.biUnion id).card=R.card at hi
      dsimp [ordinaryEndpointDemand]
      omega

#print axioms disjoint_ordinary_endpoint_demand
end
end Snake9
