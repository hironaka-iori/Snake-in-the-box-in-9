import DenseRowGroups

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

theorem row_window_endpoint_group {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : DistinctOuterConfig p a b c d) (k : Coord)
    (hk : k∈distinctR a b c d) (hbk : InPath p (pair b k))
    (ht : InPath p (triple a c k) ∧ InPath p (triple a d k))
    (hrow : ∀w,InPath p w → Adj (pair b k) w → w=triple b k c ∨ w=triple b k d)
    (hccover : ¬InPath p (pair c k) → ∀w,InPath p w → Adj (triple a c k) w →
      w=quad a b c k ∨ w=quad a c d k)
    (hdcover : ¬InPath p (quad a b d k) → ∀w,InPath p w → Adj (triple a d k) w →
      w=pair d k ∨ w=quad a c d k) :
    AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a c k) ∨
      AtMostOneNeighbor p (triple a d k) := by
  by_contra hn
  push_neg at hn
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  have hr := force_two_neighbors p (pair b k) (triple b k c) (triple b k d)
    hn.1 hrow
  have hdk : InPath p (pair d k) := by
    by_contra hndk
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
      rcases selected_three_neighbors_repeat p hq h.habd_selected ht.2 hr.2 adj1 adj2 adj3 with he | he | he
      · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
        simp [bit_triple,h.hab,Ne.symm h.hbd,hkb] at hb
      · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
        simp [bit_triple,Ne.symm h.hab,Ne.symm h.had,hka] at hb
      · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
        simp [bit_triple,Ne.symm h.hab,Ne.symm h.had,hka] at hb
    exact hndk ((force_two_neighbors p (triple a d k) (pair d k) (quad a c d k)
      hn.2.2 (hdcover hnq)).1)
  have habck : InPath p (quad a b c k) := by
    by_contra hnq
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
      rcases selected_three_neighbors_repeat p hck h.hc ht.1 hr.1 adj1 adj2 adj3 with he | he | he
      · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
        simp [bit_unit,bit_triple,Ne.symm h.hac,hka] at hb
      · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
        simp [bit_unit,bit_triple,Ne.symm h.hbc,hkb] at hb
      · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
        simp [bit_triple,Ne.symm h.hab,Ne.symm h.hac,hka] at hb
    exact hnq ((force_two_neighbors p (triple a c k) (quad a b c k) (quad a c d k)
      hn.2.1 (hccover hnck)).1)
  have hnck : ¬InPath p (pair c k) := by
    intro hc
    apply middle_row_triple_forbidden p a b k c h.hab (Ne.symm hka)
      h.hac (Ne.symm hkb) h.hbc hkc hbk
      (by simpa only [pair_comm c k] using hc)
      (by simpa only [quad_swap_last a b c k] using habck) hr.1
  have hq := (force_two_neighbors p (triple a c k) (quad a b c k) (quad a c d k)
    hn.2.1 (hccover hnck)).2
  apply selected_coordinate_cycle8_false (translate p (unit a)) a b c d k
    h.hab h.hac h.had (Ne.symm hka) h.hbc h.hbd
    (Ne.symm hkb) h.hcd (Ne.symm hkc) (Ne.symm hkd)
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using hbk
  · apply (inPath_translate_at p (unit a) _).mpr
    have ht' : InPath p (triple b c k) := by simpa only [triple_swap b k c] using hr.1
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using ht'
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using habck
  · exact (translate_pair_membership p a c k).mpr ht.1
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using hq
  · exact (translate_pair_membership p a d k).mpr ht.2
  · apply (inPath_translate_at p (unit a) _).mpr
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using hdk
  · apply (inPath_translate_at p (unit a) _).mpr
    have ht' : InPath p (triple b d k) := by simpa only [triple_swap b k d] using hr.2
    simpa only [quad,triple,pair,vxor_assoc,vxor_cancel] using ht'

#print axioms row_window_endpoint_group
end
end Snake9