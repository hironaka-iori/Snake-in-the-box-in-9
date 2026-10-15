import CommonHoleEndpointGroups

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
namespace CommonHoleConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : CommonHoleConfig p a b c d)
include h

theorem ordinary_missing_impossible (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2)
    (s : Finset Coord) (hs : s∈f.F) (hsR : s⊆distinctR a b c d) : False := by
  have hR : (distinctR a b c d).card=5 := by
    simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.outer.hab,h.outer.hac,
      h.outer.had,h.outer.hbc,h.outer.hbd,h.outer.hcd]
  have heR := (mem_distinctR a b c d h.e).mpr h.he
  obtain ⟨i,j,hij,hsij⟩ := Finset.card_eq_two.mp (f.edge_card s hs)
  have hi := hsR (show i∈s by rw [hsij]; simp)
  have hj := hsR (show j∈s by rw [hsij]; simp)
  have hm : ({i,j}:Finset Coord)∈f.F := hsij ▸ hs
  rcases common_hole_rr_cases (distinctR a b c d) h.e f.F hR heR hFcard f.edge_card s hs hsR with
    ⟨t,ht,hts,htR⟩ | ⟨k,hk,hke,hiso⟩
  · obtain ⟨k,l,hkl,htkl⟩ := Finset.card_eq_two.mp (f.edge_card t ht)
    have hk := htR (show k∈t by rw [htkl]; simp)
    have hl := htR (show l∈t by rw [htkl]; simp)
    have hn : ({k,l}:Finset Coord)∈f.F := htkl ▸ ht
    have hne : ({i,j}:Finset Coord)≠{k,l} := by rw [←hsij,←htkl]; exact Ne.symm hts
    exact h.two_ordinary_missing_false f i j k l hi hj hk hl hij hkl hm hn hne
  · exact h.ordinary_pair_and_isolated_false f i j k hi hj hij hm hk hke hiso

theorem middle_restrictions (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) :
    (∀s∈f.F,¬s⊆distinctR a b c d) ∧ ({c,d}:Finset Coord)∉f.F ∧
    (∀k,k∈distinctR a b c d→k≠h.e→¬(({c,k}:Finset Coord)∈f.F ∧ ({d,k}:Finset Coord)∈f.F)) := by
  have hRR : ∀s∈f.F,¬s⊆distinctR a b c d := fun s hs hsr => h.ordinary_missing_impossible f hFcard s hs hsr
  have hR : (distinctR a b c d).card=5 := by
    simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.outer.hab,h.outer.hac,
      h.outer.had,h.outer.hbc,h.outer.hbd,h.outer.hcd]
  have heR := (mem_distinctR a b c d h.e).mpr h.he
  have hcR : c∉distinctR a b c d := by simp [distinctR]
  have hdR : d∉distinctR a b c d := by simp [distinctR]
  refine ⟨hRR,?_,?_⟩
  · intro hm
    obtain ⟨j,hj,his⟩ := common_hole_cd_three_isolated (distinctR a b c d) h.e c d f.F
      hR heR hcR hdR hFcard f.edge_card hRR hm
    exact h.three_isolated_active_false f j hj his
  · intro k hk hke hm
    obtain ⟨j,hj,his⟩ := common_hole_double_star_three_isolated (distinctR a b c d) h.e c d k f.F
      hR heR hcR hdR h.outer.hcd hk hFcard hm.1 hm.2
    exact h.three_isolated_active_false f j hj his

theorem all_active_endpoint_groups_false
    (hep : ∀k,k∈distinctR a b c d→k≠h.e→
      ∃v,InPath p v ∧ AtMostOneNeighbor p v ∧ ActiveEndpointMember a b c d k v) : False := by
  let A := (distinctR a b c d).erase h.e
  have hR : (distinctR a b c d).card=5 := by
    simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.outer.hab,h.outer.hac,
      h.outer.had,h.outer.hbc,h.outer.hbd,h.outer.hcd]
  have heR := (mem_distinctR a b c d h.e).mpr h.he
  have hA : A.card=4 := by dsimp [A]; rw [Finset.card_erase_of_mem heR,hR]
  obtain ⟨j,hj⟩ := Function.Embedding.exists_of_card_le_finset (show Fintype.card (Fin 3)≤A.card by simp [hA])
  have hm (r : Fin 3) : j r∈distinctR a b c d ∧ j r≠h.e := by
    obtain ⟨hn,hr⟩ := Finset.mem_erase.mp (hj ⟨r,rfl⟩)
    exact ⟨hr,hn⟩
  exact three_active_endpoint_groups_false p a b c d j j.injective (fun r => (hm r).1)
    (fun r => hep (j r) (hm r).1 (hm r).2)

end CommonHoleConfig
#print axioms CommonHoleConfig.middle_restrictions
#print axioms CommonHoleConfig.all_active_endpoint_groups_false
end
end Snake9
