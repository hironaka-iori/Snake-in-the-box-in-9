import OrdinaryIsolatedGeometry
import OrdinaryOuterCountingDefs
import CommonHoleEndpointGroups

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
namespace OrdinaryOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : OrdinaryOuterConfig p a b c d)
include h

theorem isolated_central_absent (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s)
    (hcd : ({c,d}:Finset Coord)∉f.F) : ¬InPath p (quad a c d k) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have ht := h.isolated_middle_selected f k hk hisol
  have hcdSel := (f.selected_iff c d h.outer.hcd (Ne.symm h.outer.hac)
    (Ne.symm h.outer.hbc) (Ne.symm h.outer.had) (Ne.symm h.outer.hbd)).mpr hcd
  exact ordinary_quad_absent p a c d k h.outer.hac (Ne.symm h.outer.hcd)
    hh.2.2.1 (Ne.symm hh.2.2.2) hcdSel ht.1 ht.2

theorem isolated_endpoint_group_of_c_partner (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s)
    (hcd : ({c,d}:Finset Coord)∉f.F)
    (hC : ∀r∈distinctR a b c d, (({k,r}:Finset Coord)=h.A ∨ ({k,r}:Finset Coord)=h.B) → ({c,r}:Finset Coord)∉f.F) :
    AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a c k) := by
  by_contra hn
  push_neg at hn
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  have ht := h.isolated_middle_selected f k hk hisol
  have hr := force_two_neighbors p (pair b k) (triple b k c) (triple b k d)
    hn.1 (h.row_cover k hk)
  have hnck : ¬InPath p (pair c k) := by
    intro hck
    have adj1 : Adj (pair c k) (unit c) := adj_symmetric (unit_pair_adj _ _)
    have adj2 : Adj (pair c k) (triple a c k) := by
      have he : triple a c k=triple c k a := by
        apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
      rw [he]; exact pair_triple_adj _ _ _
    have adj3 : Adj (pair c k) (triple b k c) := by
      have he : triple b k c=triple c k b := by
        apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
      rw [he]; exact pair_triple_adj _ _ _
    rcases selected_three_neighbors_repeat p hck h.outer.hc ht.1 hr.1 adj1 adj2 adj3 with he | he | he
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_unit,bit_triple,Ne.symm h.outer.hac,hka] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
      simp [bit_unit,bit_triple,Ne.symm h.outer.hbc,hkb] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_triple,Ne.symm h.outer.hab,Ne.symm h.outer.hac,hka] at hb
  exact h.isolated_central_absent f k hk hisol hcd
    ((force_two_neighbors p (triple a c k) (quad a b c k) (quad a c d k)
      hn.2 (h.isolated_c_cover f k hk hisol hC hnck)).2)

theorem isolated_endpoint_group_of_d_partner (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s)
    (hcd : ({c,d}:Finset Coord)∉f.F)
    (hD : ∀r∈distinctR a b c d, (({k,r}:Finset Coord)=h.A ∨ ({k,r}:Finset Coord)=h.B) → ({d,r}:Finset Coord)∉f.F) :
    AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a d k) := by
  by_contra hn
  push_neg at hn
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  have ht := h.isolated_middle_selected f k hk hisol
  have hr := force_two_neighbors p (pair b k) (triple b k c) (triple b k d)
    hn.1 (h.row_cover k hk)
  have hnq : ¬InPath p (quad a b d k) := by
    intro hq
    have adj1 : Adj (quad a b d k) (triple a b d) := adj_symmetric (triple_quad_adj _ _ _ _)
    have adj2 : Adj (quad a b d k) (triple a d k) := by
      have he : quad a b d k=quad a d k b := by
        apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
      rw [he]; exact adj_symmetric (triple_quad_adj _ _ _ _)
    have adj3 : Adj (quad a b d k) (triple b k d) := by
      have he : quad a b d k=quad b k d a := by
        apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
      rw [he]; exact adj_symmetric (triple_quad_adj _ _ _ _)
    rcases selected_three_neighbors_repeat p hq h.outer.habd_selected ht.2 hr.2 adj1 adj2 adj3 with he | he | he
    · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
      simp [bit_triple,h.outer.hab,Ne.symm h.outer.hbd,hkb] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_triple,Ne.symm h.outer.hab,Ne.symm h.outer.had,hka] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_triple,Ne.symm h.outer.hab,Ne.symm h.outer.had,hka] at hb
  exact h.isolated_central_absent f k hk hisol hcd
    ((force_two_neighbors p (triple a d k) (pair d k) (quad a c d k)
      hn.2 (h.isolated_d_cover f k hk hisol hD hnq)).2)

theorem good_row_endpoint (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d)
    (hgood : OrdinaryGoodRow f.F (distinctR a b c d) h.A h.B c d k) :
    ∃v,InPath p v ∧ AtMostOneNeighbor p v ∧ ActiveEndpointMember a b c d k v := by
  obtain ⟨his,hgood⟩ := hgood
  have ht := h.isolated_middle_selected f k hk his
  have hl : AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a c k) ∨
      AtMostOneNeighbor p (triple a d k) := by
    rcases hgood with ⟨hC,hD⟩ | ⟨hcd,hC | hD⟩
    · exact h.isolated_endpoint_group_of_partners f k hk his hC hD
    · rcases h.isolated_endpoint_group_of_c_partner f k hk his hcd hC with hl | hl
      · exact Or.inl hl
      · exact Or.inr (Or.inl hl)
    · rcases h.isolated_endpoint_group_of_d_partner f k hk his hcd hD with hl | hl
      · exact Or.inl hl
      · exact Or.inr (Or.inr hl)
  rcases hl with hl | hl | hl
  · exact ⟨pair b k,h.row_selected k hk,hl,Or.inl rfl⟩
  · exact ⟨triple a c k,ht.1,hl,Or.inr (Or.inl rfl)⟩
  · exact ⟨triple a d k,ht.2,hl,Or.inr (Or.inr (Or.inl rfl))⟩

end OrdinaryOuterConfig
#print axioms OrdinaryOuterConfig.good_row_endpoint
#print axioms OrdinaryOuterConfig.isolated_endpoint_group_of_c_partner
#print axioms OrdinaryOuterConfig.isolated_endpoint_group_of_d_partner
end
end Snake9
