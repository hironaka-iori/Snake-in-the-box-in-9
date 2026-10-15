import SingleDeltaBase

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

namespace SingleDeltaConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SingleDeltaConfig p a b c d)
include h

theorem fresh_row_selected (z : Coord)
    (hz : z≠a ∧ z≠b ∧ z≠c ∧ z≠d ∧ z≠h.i ∧ z≠h.j ∧ z≠h.k) :
    InPath p (pair b z) := by
  apply (h.outer.left.selected_iff b z (Ne.symm hz.2.1) (Ne.symm h.outer.hab)
    h.outer.hbc hz.1 hz.2.2.1).mpr
  rw [h.left_eq]
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨delta_pair_ne_right b z b d hz.2.1 hz.2.2.2.1,
    delta_pair_ne_right b z h.i h.j hz.2.2.2.2.1 hz.2.2.2.2.2.1⟩

theorem fresh_row_low (z : Coord)
    (hz : z≠a ∧ z≠b ∧ z≠c ∧ z≠d ∧ z≠h.i ∧ z≠h.j ∧ z≠h.k) :
    AtMostOneNeighbor p (pair b z) := by
  obtain ⟨hza,hzb,hzc,hzd,hzi,hzj,hzk⟩ := hz
  have hbz := h.fresh_row_selected z ⟨hza,hzb,hzc,hzd,hzi,hzj,hzk⟩
  have hq : InPath p (quad a b c z) := by
    apply (h.outer.right_pair_iff c z (Ne.symm hzc) (Ne.symm h.outer.hbc)
      h.outer.hcd hzb hzd).mpr
    rw [h.right_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨delta_pair_ne_right c z h.i h.j hzi hzj,
      delta_pair_ne_right c z c h.k hzc hzk⟩
  have hno_c : ¬InPath p (triple b z c) := by
    intro ht
    have he : triple b z c=triple b c z := triple_swap _ _ _
    have hqa : quad a b c z=quad b z c a := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    rcases selected_three_neighbors_repeat p ht hbz h.selected_bc hq
      (adj_symmetric (pair_triple_adj b z c))
      (by rw [he]; exact adj_symmetric (pair_triple_adj b c z))
      (by rw [hqa]; exact triple_quad_adj b z c a) with hh | hh | hh
    · exact hzc (pair_injective_right b z c hh)
    · have hh' := congrArg (fun v : Vertex => v.val.testBit a.val) hh
      simp [bit_pair,bit_quad,Ne.symm h.outer.hab,Ne.symm h.outer.hac,hza] at hh'
    · have hh' := congrArg (fun v : Vertex => v.val.testBit a.val) hh
      simp [bit_pair,bit_quad,Ne.symm h.outer.hab,Ne.symm h.outer.hac,hza] at hh'
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (pair b z) w) :
      w=triple b z d := by
    rcases h.outer.row_neighbor_cover z ((mem_distinctR a b c d z).mpr
      ⟨hza,hzb,hzc,hzd⟩) w hw hadj with he | he | ⟨r,hr,hrz,he⟩
    · exact False.elim (hno_c (he ▸ hw))
    · exact he
    · obtain ⟨hra,hrb,hrc,hrd⟩ := (mem_distinctR a b c d r).mp hr
      have hbr : InPath p (pair b r) := by
        apply (h.outer.left.selected_iff b r (Ne.symm hrb) (Ne.symm h.outer.hab)
          h.outer.hbc hra hrc).mpr
        rw [h.left_eq]
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨delta_pair_ne_right b r b d hrb hrd,
          delta_pair_ne b r h.i h.j (Ne.symm h.hi.2.1) (Ne.symm h.hj.2.1)⟩
      have hzr : InPath p (pair z r) := by
        apply (h.outer.left.selected_iff z r (Ne.symm hrz) hza hzc hra hrc).mpr
        rw [h.left_eq]
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
        exact ⟨delta_pair_ne z r b d hzb hzd,delta_pair_ne z r h.i h.j hzi hzj⟩
      exact False.elim (selected_triple_forbidden p b z r (Ne.symm hzb)
        (Ne.symm hrb) (Ne.symm hrz) hbz hbr hzr (he ▸ hw))
  intro x y hx hy hax hay
  exact (unique x hx hax).trans (unique y hy hay).symm

theorem triple_not_low (x y : Coord) (hxa : x≠a) (hya : y≠a)
    (ht : InPath p (triple a x y)) : ¬AtMostOneNeighbor p (triple a x y) := by
  obtain ⟨j,hj,hinj⟩ := exists_two_coords_outside_seven a b c d h.i h.j h.k
  have hu := hj 0
  have hv := hj 1
  have huv : j 0≠j 1 := fun he => (by decide : (0:Fin 2)≠1) (hinj he)
  intro hl
  have htu : triple a x y≠pair b (j 0) := by
    intro he
    have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
    simp [bit_triple,bit_pair,hxa,hya,Ne.symm h.outer.hab,hu.1] at hb
  have htv : triple a x y≠pair b (j 1) := by
    intro he
    have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
    simp [bit_triple,bit_pair,hxa,hya,Ne.symm h.outer.hab,hv.1] at hb
  rcases three_low_degree_vertices_repeat p (h.fresh_row_selected (j 0) hu)
    (h.fresh_row_selected (j 1) hv) ht (h.fresh_row_low (j 0) hu)
    (h.fresh_row_low (j 1) hv) hl with he | he | he
  · exact huv (pair_injective_right b (j 0) (j 1) he)
  · exact htu he.symm
  · exact htv he.symm

end SingleDeltaConfig
#print axioms SingleDeltaConfig.fresh_row_low
#print axioms SingleDeltaConfig.triple_not_low
end
end Snake9
