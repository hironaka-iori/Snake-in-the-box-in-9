import StarLeftGeometry
import CommonHoleEndpointGroups

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

namespace StarLeftConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : StarLeftConfig p a b c d)
include h

theorem missing_e_partner_present (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2)
    (hep : ∀k∈distinctR a b c d,(∀s∈f.F,k∉s) →
      ∃v,InPath p v ∧ AtMostOneNeighbor p v ∧ ActiveEndpointMember a b c d k v)
    (k : Coord) (hk : k∈distinctR a b c d) (hke : k≠h.e)
    (hm : ({h.e,k}:Finset Coord)∈f.F) : ({d,k}:Finset Coord)∉f.F := by
  intro hd
  have heR := (mem_distinctR a b c d h.e).mp h.he
  have hkR := (mem_distinctR a b c d k).mp hk
  have hne : ({h.e,k}:Finset Coord)≠{d,k} := by
    intro he
    have hdm : d∈({h.e,k}:Finset Coord) := he.symm ▸ (by simp)
    simpa [Ne.symm heR.2.2.2,Ne.symm hkR.2.2.2] using hdm
  have hsub : ({{h.e,k},{d,k}}:Finset (Finset Coord))⊆f.F := by
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hm
    · exact Finset.mem_singleton.mp hs ▸ hd
  have hFeq : f.F={{h.e,k},{d,k}} :=
    (Finset.eq_of_subset_of_card_le hsub (by simp [hFcard,hne])).symm
  have hcover : distinctR a b c d∩f.F.biUnion id⊆({h.e,k}:Finset Coord) := by
    intro r hr
    obtain ⟨hrR,hrU⟩ := Finset.mem_inter.mp hr
    have hrd := ((mem_distinctR a b c d r).mp hrR).2.2.2
    have hU : f.F.biUnion id=({h.e,k}:Finset Coord)∪{d,k} := by simp [hFeq]
    rw [hU] at hrU
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hrU ⊢
    tauto
  have hsmall : (distinctR a b c d∩f.F.biUnion id).card≤2 :=
    (Finset.card_le_card hcover).trans Finset.card_le_two
  have hR : (distinctR a b c d).card=5 := by
    simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.outer.hab,h.outer.hac,
      h.outer.had,h.outer.hbc,h.outer.hbd,h.outer.hcd]
  obtain ⟨u,hinj,hu⟩ := family_isolated_embedding f.F (distinctR a b c d) 3 (by omega)
  exact three_active_endpoint_groups_false p a b c d u hinj (fun r => (hu r).1)
    (fun r => hep (u r) (hu r).1 (hu r).2)

theorem missing_ordinary_endpoint (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2)
    (hep : ∀k∈distinctR a b c d,(∀s∈f.F,k∉s) →
      ∃v,InPath p v ∧ AtMostOneNeighbor p v ∧ ActiveEndpointMember a b c d k v)
    (s : Finset Coord) (hs : s∈f.F) (hsR : s⊆distinctR a b c d) :
    ∃v,InPath p v ∧ AtMostOneNeighbor p v ∧
      (v=edgeVertex s ∨ ∃k∈distinctR a b c d,k≠h.e ∧ s={h.e,k} ∧ v=pair b k) := by
  by_cases he : h.e∈s
  · obtain ⟨k,hke,rfl⟩ := two_element_set_with_member s h.e (f.edge_card s hs) he
    have hk : k∈distinctR a b c d := hsR (by simp)
    have hd := h.missing_e_partner_present f hFcard hep k hk hke hs
    rcases h.missing_e_endpoint_group f k hk hke hs hd with hl | hl
    · exact ⟨pair b k,h.row_selected k hk,hl,Or.inr ⟨k,hk,hke,rfl,rfl⟩⟩
    · exact ⟨pair h.e k,h.ordinary_pair h.e k h.he hk (Ne.symm hke),hl,
        Or.inl (edgeVertex_pair h.e k (Ne.symm hke)).symm⟩
  · obtain ⟨i,j,hij,rfl,hv⟩ := edgeVertex_eq_pair s (f.edge_card s hs)
    have hi := hsR (by simp : i∈({i,j}:Finset Coord))
    have hj := hsR (by simp : j∈({i,j}:Finset Coord))
    have hie : i≠h.e := by intro hh; exact he (by simp [hh])
    have hje : j≠h.e := by intro hh; exact he (by simp [hh])
    exact ⟨pair i j,h.ordinary_pair i j hi hj hij,
      h.missing_pair_low f i j hi hj hij hie hje hs,Or.inl hv.symm⟩

end StarLeftConfig
#print axioms StarLeftConfig.missing_ordinary_endpoint
end
end Snake9
