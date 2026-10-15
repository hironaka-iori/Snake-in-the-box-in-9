import OrdinaryMissingStar

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
namespace OrdinaryOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : OrdinaryOuterConfig p a b c d)
include h

theorem missing_d_row_endpoint_of_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d)
    (hck : ({c,k}:Finset Coord)∉f.F)
    (hcd : ({c,d}:Finset Coord)∉f.F)
    (hspokes : ∀r∈distinctR a b c d,r≠k → ({k,r}:Finset Coord)∉f.F)
    (hpartner : ∀r∈distinctR a b c d, (({k,r}:Finset Coord)=h.A ∨ ({k,r}:Finset Coord)=h.B) → ({c,r}:Finset Coord)∉f.F)
    (hcover : ∀w,InPath p w → Adj (pair d k) w → w=triple b d k ∨ w=triple c d k) :
    AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a c k) ∨
      AtMostOneNeighbor p (pair d k) := by
  by_contra hn
  push_neg at hn
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  have htc := (f.selected_iff c k (Ne.symm hkc) (Ne.symm h.outer.hac)
    (Ne.symm h.outer.hbc) hka hkb).mpr hck
  have htcd := (f.selected_iff c d h.outer.hcd (Ne.symm h.outer.hac)
    (Ne.symm h.outer.hbc) (Ne.symm h.outer.had) (Ne.symm h.outer.hbd)).mpr hcd
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
    rcases selected_three_neighbors_repeat p hck h.outer.hc htc hr.1 adj1 adj2 adj3 with he | he | he
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_unit,bit_triple,Ne.symm h.outer.hac,hka] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
      simp [bit_unit,bit_triple,Ne.symm h.outer.hbc,hkb] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_triple,Ne.symm h.outer.hab,Ne.symm h.outer.hac,hka] at hb
  have hq := (force_two_neighbors p (triple a c k) (quad a b c k) (quad a c d k)
    hn.2.1 (h.partial_c_cover f k hk hck hspokes hpartner hnck)).2
  have hcdk := (force_two_neighbors p (pair d k) (triple b d k) (triple c d k)
    hn.2.2 hcover).2
  have hno := ordinary_quad_absent p c a d k (Ne.symm h.outer.hac)
    (Ne.symm h.outer.had) hka (Ne.symm hkd)
    (by simpa only [triple,pair_comm c a] using htcd)
    (by simpa only [triple,pair_comm c a] using htc) hcdk
  exact hno (by simpa only [quad_swap_first a c d k] using hq)

end OrdinaryOuterConfig
#print axioms OrdinaryOuterConfig.missing_d_row_endpoint_of_cover
end
end Snake9
