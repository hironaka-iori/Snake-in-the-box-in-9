import SharedCentralCSelected

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem ce_de_false (f : MissingAtNeighbor p a b) (hF : f.F={{c,h.e},{d,h.e}}) : False := by
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hs := h.central_c_pair_selected f hF
  have hacd := h.ce_de_middle_without_e f hF c d h.ordinary.outer.hcd
    (Ne.symm h.ordinary.outer.hac) (Ne.symm h.ordinary.outer.hbc) (Ne.symm he.2.2.1)
    (Ne.symm h.ordinary.outer.had) (Ne.symm h.ordinary.outer.hbd) (Ne.symm he.2.2.2)
  have hcde := h.ce_de_cde_selected f hF
  have adj1 : Adj (pair c d) (unit c) := adj_symmetric (unit_pair_adj _ _)
  have adj2 : Adj (pair c d) (triple a c d) := by
    rw [←triple_rotate c d a]; exact pair_triple_adj _ _ _
  rcases selected_three_neighbors_repeat p hs h.ordinary.outer.hc hacd hcde
    adj1 adj2 (pair_triple_adj _ _ _) with hh | hh | hh
  · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) hh
    simp [bit_unit,bit_triple,Ne.symm h.ordinary.outer.hac,Ne.symm h.ordinary.outer.had] at hb
  · have hb := congrArg (fun z : Vertex => z.val.testBit h.e.val) hh
    simp [bit_unit,bit_triple,Ne.symm he.2.2.1,Ne.symm he.2.2.2] at hb
  · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) hh
    simp [bit_triple,Ne.symm h.ordinary.outer.hac,Ne.symm h.ordinary.outer.had,he.1] at hb

end SharedOuterConfig
#print axioms SharedOuterConfig.ce_de_false
end
end Snake9
