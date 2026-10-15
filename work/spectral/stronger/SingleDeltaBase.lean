import DistinctOuterConfig
import SingleDeltaResources
import ExtraFreshCoordinates

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

theorem delta_pair_ne (x y r s : Coord) (hxr : x≠r) (hxs : x≠s) :
    ({x,y}:Finset Coord)≠{r,s} := by
  intro he
  have hh : x∈({r,s}:Finset Coord) := he ▸ (by simp : x∈({x,y}:Finset Coord))
  simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  exact hh.elim hxr hxs

theorem delta_pair_ne_right (x y r s : Coord) (hyr : y≠r) (hys : y≠s) :
    ({x,y}:Finset Coord)≠{r,s} := by
  rw [Finset.pair_comm x y]
  exact delta_pair_ne y x r s hyr hys

structure SingleDeltaConfig {m : Nat} (p : Snake m) (a b c d : Coord) where
  outer : DistinctOuterConfig p a b c d
  i : Coord
  j : Coord
  k : Coord
  hi : i≠a ∧ i≠b ∧ i≠c ∧ i≠d
  hj : j≠a ∧ j≠b ∧ j≠c ∧ j≠d
  hk : k≠a ∧ k≠b ∧ k≠c ∧ k≠d
  hij : i≠j
  hik : i≠k
  hjk : j≠k
  left_eq : outer.left.F={{b,d},{i,j}}
  right_eq : outer.right.F={{i,j},{c,k}}

namespace SingleDeltaConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SingleDeltaConfig p a b c d)
include h

theorem absent_pair_a (r : Coord) (hra : r≠a) (hrb : r≠b) : ¬InPath p (pair a r) := by
  intro hr
  have hza : InPath (translate p (unit a)) (unit a) :=
    (translate_unit_membership p a a).mpr (by simpa only [pair_self] using h.outer.hzero)
  have hzb := (translate_unit_membership p a b).mpr h.outer.hab_selected
  have hz0 : InPath (translate p (unit a)) 0 :=
    (inPath_translate_at p (unit a) 0).mpr (by simpa using h.outer.ha)
  rcases unit_cover_two (translate p (unit a)) a b hz0 hza hzb h.outer.hab r
    ((translate_unit_membership p a r).mpr hr) with he | he
  · exact hra he
  · exact hrb he

theorem selected_bc : InPath p (pair b c) := by
  have hn : ({a,c}:Finset Coord)∉h.outer.right.F := by
    rw [h.right_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨delta_pair_ne a c h.i h.j (Ne.symm h.hi.1) (Ne.symm h.hj.1),
      delta_pair_ne a c c h.k h.outer.hac (Ne.symm h.hk.1)⟩
  have hs := (h.outer.right_pair_iff a c h.outer.hac h.outer.hab h.outer.had
    (Ne.symm h.outer.hbc) h.outer.hcd).mpr hn
  simpa only [quad_swap_last a b a c,quad_cancel_first] using hs

theorem absent_pair_c (r : Coord) (hrc : r≠c) (hrb : r≠b) : ¬InPath p (pair c r) := by
  intro hr
  have hp : InPath p (pair c b) := by simpa only [pair_comm b c] using h.selected_bc
  rcases selected_three_neighbors_repeat p h.outer.hc h.outer.hzero hp hr
    (adj_symmetric ((adj_zero_iff _).mpr ⟨c,rfl⟩)) (unit_pair_adj c b) (unit_pair_adj c r)
    with he | he | he
  · exact pair_nonzero c b (Ne.symm h.outer.hbc) he.symm
  · exact pair_nonzero c r (Ne.symm hrc) he.symm
  · exact hrb (pair_injective_right c b r he).symm

theorem saturated_outer (x y r : Coord)
    (hxa : x≠a) (hxb : x≠b) (hya : y≠a) (hyb : y≠b)
    (hra : r≠a) (hrb : r≠b)
    (hp : InPath p (pair x y)) (hq : InPath p (quad a b x y))
    (ht : InPath p (triple a x y)) : ¬InPath p (quad a x y r) := by
  intro hs
  have heq : quad a b x y=quad a x y b := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  have het : triple a x y=triple x y a := by
    apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
  rcases selected_three_neighbors_repeat p ht hp hq hs
    (by rw [het]; exact adj_symmetric (pair_triple_adj x y a))
    (by rw [heq]; exact triple_quad_adj a x y b)
    (triple_quad_adj a x y r) with he | he | he
  · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
    simp [bit_pair,bit_quad,Ne.symm h.outer.hab,hxa,hya] at hb
  · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
    simp [bit_pair,bit_quad,hxa,hya,hra] at hb
  · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
    simp [bit_quad,h.outer.hab,hxb,hyb,hrb] at hb

theorem selected_outer_k (r : Coord) (hra : r≠a) (hrb : r≠b)
    (hrc : r≠c) (hrd : r≠d) (hrk : r≠h.k) :
    InPath p (pair h.k r) ∧ InPath p (quad a b h.k r) := by
  constructor
  · apply (h.outer.left.selected_iff h.k r (Ne.symm hrk) h.hk.1 h.hk.2.2.1 hra hrc).mpr
    rw [h.left_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨delta_pair_ne h.k r b d h.hk.2.1 h.hk.2.2.2,
      delta_pair_ne h.k r h.i h.j (Ne.symm h.hik) (Ne.symm h.hjk)⟩
  · apply (h.outer.right_pair_iff h.k r (Ne.symm hrk) h.hk.2.1 h.hk.2.2.2 hrb hrd).mpr
    rw [h.right_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨delta_pair_ne h.k r h.i h.j (Ne.symm h.hik) (Ne.symm h.hjk),
      delta_pair_ne_right h.k r c h.k hrc hrk⟩

theorem selected_outer_i (r : Coord) (hra : r≠a) (hrb : r≠b)
    (hrc : r≠c) (hrd : r≠d) (hri : r≠h.i) (hrj : r≠h.j) :
    InPath p (pair h.i r) ∧ InPath p (quad a b h.i r) := by
  constructor
  · apply (h.outer.left.selected_iff h.i r (Ne.symm hri) h.hi.1 h.hi.2.2.1 hra hrc).mpr
    rw [h.left_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨delta_pair_ne h.i r b d h.hi.2.1 h.hi.2.2.2,
      delta_pair_ne_right h.i r h.i h.j hri hrj⟩
  · apply (h.outer.right_pair_iff h.i r (Ne.symm hri) h.hi.2.1 h.hi.2.2.2 hrb hrd).mpr
    rw [h.right_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨delta_pair_ne_right h.i r h.i h.j hri hrj,
      delta_pair_ne h.i r c h.k h.hi.2.2.1 h.hik⟩

theorem selected_outer_j (r : Coord) (hra : r≠a) (hrb : r≠b)
    (hrc : r≠c) (hrd : r≠d) (hri : r≠h.i) (hrj : r≠h.j) :
    InPath p (pair h.j r) ∧ InPath p (quad a b h.j r) := by
  constructor
  · apply (h.outer.left.selected_iff h.j r (Ne.symm hrj) h.hj.1 h.hj.2.2.1 hra hrc).mpr
    rw [h.left_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨delta_pair_ne h.j r b d h.hj.2.1 h.hj.2.2.2,
      delta_pair_ne_right h.j r h.i h.j hri hrj⟩
  · apply (h.outer.right_pair_iff h.j r (Ne.symm hrj) h.hj.2.1 h.hj.2.2.2 hrb hrd).mpr
    rw [h.right_eq]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨delta_pair_ne_right h.j r h.i h.j hri hrj,
      delta_pair_ne h.j r c h.k h.hj.2.2.1 h.hjk⟩

end SingleDeltaConfig
#print axioms SingleDeltaConfig.selected_outer_k
end
end Snake9
