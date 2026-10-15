import MixedIsolatedGeometry

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
namespace MixedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : MixedOuterConfig p a b c d)
include h

theorem isolated_central_absent (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s)
    (hcd : ({c,d}:Finset Coord)∉f.F) : ¬InPath p (quad a c d k) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have ht := h.isolated_middle_selected f k hk hisol
  have hcdSel := (f.selected_iff c d h.left.outer.hcd (Ne.symm h.left.outer.hac)
    (Ne.symm h.left.outer.hbc) (Ne.symm h.left.outer.had) (Ne.symm h.left.outer.hbd)).mpr hcd
  exact ordinary_quad_absent p a c d k h.left.outer.hac (Ne.symm h.left.outer.hcd)
    hh.2.2.1 (Ne.symm hh.2.2.2) hcdSel ht.1 ht.2

theorem isolated_endpoint_group_of_c_partner (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s)
    (hcd : ({c,d}:Finset Coord)∉f.F)
    (hC : ∀r∈distinctR a b c d, ({k,r}:Finset Coord)={h.i,h.j} → ({c,r}:Finset Coord)∉f.F) :
    AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a c k) := by
  by_contra hn
  push_neg at hn
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  have ht := h.isolated_middle_selected f k hk hisol
  have hr := force_two_neighbors p (pair b k) (triple b k c) (triple b k d)
    hn.1 (h.left.row_cover k hk)
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
    rcases selected_three_neighbors_repeat p hck h.left.outer.hc ht.1 hr.1 adj1 adj2 adj3 with he | he | he
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_unit,bit_triple,Ne.symm h.left.outer.hac,hka] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
      simp [bit_unit,bit_triple,Ne.symm h.left.outer.hbc,hkb] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_triple,Ne.symm h.left.outer.hab,Ne.symm h.left.outer.hac,hka] at hb
  exact h.isolated_central_absent f k hk hisol hcd
    ((force_two_neighbors p (triple a c k) (quad a b c k) (quad a c d k)
      hn.2 (h.isolated_c_cover f k hk hisol hC hnck)).2)

theorem isolated_endpoint_group_of_d_partner (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s)
    (hcd : ({c,d}:Finset Coord)∉f.F)
    (hD : ∀r∈distinctR a b c d, ({k,r}:Finset Coord)={h.i,h.j} → ({d,r}:Finset Coord)∉f.F) :
    AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a d k) := by
  by_contra hn
  push_neg at hn
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  have ht := h.isolated_middle_selected f k hk hisol
  have hr := force_two_neighbors p (pair b k) (triple b k c) (triple b k d)
    hn.1 (h.left.row_cover k hk)
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
    rcases selected_three_neighbors_repeat p hq h.left.outer.habd_selected ht.2 hr.2 adj1 adj2 adj3 with he | he | he
    · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
      simp [bit_triple,h.left.outer.hab,Ne.symm h.left.outer.hbd,hkb] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_triple,Ne.symm h.left.outer.hab,Ne.symm h.left.outer.had,hka] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_triple,Ne.symm h.left.outer.hab,Ne.symm h.left.outer.had,hka] at hb
  exact h.isolated_central_absent f k hk hisol hcd
    ((force_two_neighbors p (triple a d k) (pair d k) (quad a c d k)
      hn.2 (h.isolated_d_cover f k hk hisol hD hnq)).2)

end MixedOuterConfig
#print axioms MixedOuterConfig.isolated_endpoint_group_of_c_partner
#print axioms MixedOuterConfig.isolated_endpoint_group_of_d_partner
end
end Snake9
