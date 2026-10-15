import MixedPartnerCounting
import MixedIsolatedOneSide
import CommonHoleEndpointGroups

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
namespace MixedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : MixedOuterConfig p a b c d)
include h

theorem endpoint_of_isolated_low (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (his : PairIsolated f.F k)
    (hl : AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a c k) ∨
      AtMostOneNeighbor p (triple a d k)) :
    ∃v,InPath p v ∧ AtMostOneNeighbor p v ∧ ActiveEndpointMember a b c d k v := by
  have ht := h.isolated_middle_selected f k hk his
  rcases hl with hl | hl | hl
  · exact ⟨pair b k,h.left.row_selected k hk,hl,Or.inl rfl⟩
  · exact ⟨triple a c k,ht.1,hl,Or.inr (Or.inl rfl)⟩
  · exact ⟨triple a d k,ht.2,hl,Or.inr (Or.inr (Or.inl rfl))⟩

theorem clean_isolated_endpoint (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d\{h.i,h.j}) (his : PairIsolated f.F k) :
    ∃v,InPath p v ∧ AtMostOneNeighbor p v ∧ ActiveEndpointMember a b c d k v := by
  obtain ⟨hkR,hkN⟩ := Finset.mem_sdiff.mp hk
  have bad (r : Coord) (he : ({k,r}:Finset Coord)={h.i,h.j}) : False :=
    hkN (he ▸ (by simp : k∈({k,r}:Finset Coord)))
  apply h.endpoint_of_isolated_low f k hkR his
  exact h.isolated_endpoint_group_of_partners f k hkR his
    (fun r _ he => False.elim (bad r he)) (fun r _ he => False.elim (bad r he))

theorem clean_touched (f : MissingAtNeighbor p a b) :
    ∃s∈f.F,∃z∈s,z∈distinctR a b c d\{h.i,h.j} := by
  by_contra hn
  let C := distinctR a b c d\{h.i,h.j}
  have hR : (distinctR a b c d).card=5 := by
    simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.left.outer.hab,h.left.outer.hac,
      h.left.outer.had,h.left.outer.hbc,h.left.outer.hbd,h.left.outer.hcd]
  have hsub : ({h.i,h.j}:Finset Coord)⊆distinctR a b c d := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h.hi
    · exact Finset.mem_singleton.mp hx ▸ h.hj
  have hC : C.card=3 := by simp [C,Finset.card_sdiff hsub,hR,h.hij]
  have his (k : Coord) (hk : k∈C) : PairIsolated f.F k :=
    fun s hs hks => hn ⟨s,hs,k,hks,hk⟩
  obtain ⟨u,hu⟩ := Function.Embedding.exists_of_card_le_finset
    (show Fintype.card (Fin 3)≤C.card by simp [hC])
  apply three_active_endpoint_groups_false p a b c d u u.injective
    (fun r => (Finset.mem_sdiff.mp (hu ⟨r,rfl⟩)).1)
  intro r
  exact h.clean_isolated_endpoint f (u r) (hu ⟨r,rfl⟩) (his _ (hu ⟨r,rfl⟩))

theorem isolated_endpoint (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) (k : Coord)
    (hk : k∈distinctR a b c d) (his : PairIsolated f.F k) :
    ∃v,InPath p v ∧ AtMostOneNeighbor p v ∧ ActiveEndpointMember a b c d k v := by
  apply h.endpoint_of_isolated_low f k hk his
  rcases h.partner_alternative f hFcard (h.clean_touched f) k with ⟨hC,hD⟩ | ⟨hcd,hC | hD⟩
  · exact h.isolated_endpoint_group_of_partners f k hk his hC hD
  · rcases h.isolated_endpoint_group_of_c_partner f k hk his hcd hC with hl | hl
    · exact Or.inl hl
    · exact Or.inr (Or.inl hl)
  · rcases h.isolated_endpoint_group_of_d_partner f k hk his hcd hD with hl | hl
    · exact Or.inl hl
    · exact Or.inr (Or.inr hl)

end MixedOuterConfig
#print axioms MixedOuterConfig.clean_touched
#print axioms MixedOuterConfig.isolated_endpoint
end
end Snake9
