import OrdinaryTwoEndpoints

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section

namespace OrdinaryOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : OrdinaryOuterConfig p a b c d)
include h

theorem nonlow_outside_group_members (f : MissingAtNeighbor p a b) (u v : Coord)
    (hu : u∈distinctR a b c d) (hv : v∈distinctR a b c d) (huv : u≠v)
    (hU : OrdinaryGoodRow f.F (distinctR a b c d) h.A h.B c d u)
    (hV : OrdinaryGoodRow f.F (distinctR a b c d) h.A h.B c d v)
    (w : Vertex) (hw : InPath p w)
    (hwu : ¬ActiveEndpointMember a b c d u w)
    (hwv : ¬ActiveEndpointMember a b c d v w) : ¬AtMostOneNeighbor p w := by
  obtain ⟨x,hx,hlx,hgx⟩ := h.good_row_endpoint f u hu hU
  obtain ⟨y,hy,hly,hgy⟩ := h.good_row_endpoint f v hv hV
  have hxy := active_endpoint_groups_disjoint a b c d u v hu huv x y hgx hgy
  intro hlw
  rcases three_low_degree_vertices_repeat p hx hy hw hlx hly hlw with he | he | he
  · exact hxy he
  · exact hwu (he ▸ hgx)
  · exact hwv (he ▸ hgy)

theorem nonlow_two_ordinary_bits (f : MissingAtNeighbor p a b) (u v : Coord)
    (hu : u∈distinctR a b c d) (hv : v∈distinctR a b c d) (huv : u≠v)
    (hU : OrdinaryGoodRow f.F (distinctR a b c d) h.A h.B c d u)
    (hV : OrdinaryGoodRow f.F (distinctR a b c d) h.A h.B c d v)
    (w : Vertex) (hw : InPath p w) (i j : Coord)
    (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d) (hij : i≠j)
    (hwi : w.val.testBit i.val=true) (hwj : w.val.testBit j.val=true) :
    ¬AtMostOneNeighbor p w := by
  have outside (k : Coord) : ¬ActiveEndpointMember a b c d k w := by
    intro hg
    by_cases hik : i=k
    · have hjk : j≠k := by intro hjk; exact hij (hik.trans hjk.symm)
      have hb := active_endpoint_other_bit a b c d j k hj hjk w hg
      rw [hwj] at hb; contradiction
    · have hb := active_endpoint_other_bit a b c d i k hi hik w hg
      rw [hwi] at hb; contradiction
  exact h.nonlow_outside_group_members f u v hu hv huv hU hV w hw (outside u) (outside v)

end OrdinaryOuterConfig
#print axioms OrdinaryOuterConfig.nonlow_two_ordinary_bits
end
end Snake9
