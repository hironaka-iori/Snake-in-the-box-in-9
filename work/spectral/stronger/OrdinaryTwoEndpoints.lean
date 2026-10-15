import OrdinaryIsolatedOneSide

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section

namespace OrdinaryOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : OrdinaryOuterConfig p a b c d)
include h

theorem nonlow_outside_two (f : MissingAtNeighbor p a b) (u v : Coord)
    (hu : u∈distinctR a b c d) (hv : v∈distinctR a b c d) (huv : u≠v)
    (hU : OrdinaryGoodRow f.F (distinctR a b c d) h.A h.B c d u)
    (hV : OrdinaryGoodRow f.F (distinctR a b c d) h.A h.B c d v)
    (w : Vertex) (hw : InPath p w)
    (hwu : w.val.testBit u.val=false) (hwv : w.val.testBit v.val=false) :
    ¬AtMostOneNeighbor p w := by
  obtain ⟨x,hx,hlx,hgx⟩ := h.good_row_endpoint f u hu hU
  obtain ⟨y,hy,hly,hgy⟩ := h.good_row_endpoint f v hv hV
  have hxy := active_endpoint_groups_disjoint a b c d u v hu huv x y hgx hgy
  have hxw : x≠w := by
    intro he
    have hb := active_endpoint_bit a b c d u hu x hgx
    rw [he,hwu] at hb
    contradiction
  have hyw : y≠w := by
    intro he
    have hb := active_endpoint_bit a b c d v hv y hgy
    rw [he,hwv] at hb
    contradiction
  intro hlw
  rcases three_low_degree_vertices_repeat p hx hy hw hlx hly hlw with he | he | he
  · exact hxy he
  · exact hxw he
  · exact hyw he

end OrdinaryOuterConfig
#print axioms OrdinaryOuterConfig.nonlow_outside_two
end
end Snake9
