import CommonHoleIsolated
import DistinctOuterMirror

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

theorem low_of_translate {m : Nat} (p : Snake m) (t v : Vertex)
    (h : AtMostOneNeighbor (translate p t) v) : AtMostOneNeighbor p (vxor t v) := by
  intro x y hx hy hax hay
  apply vxor_injective t
  apply h (vxor t x) (vxor t y)
  · exact (inPath_translate_iff p t x).mpr hx
  · exact (inPath_translate_iff p t y).mpr hy
  · simpa only [vxor_cancel] using (adj_vxor t (vxor t v) x).mpr hax
  · simpa only [vxor_cancel] using (adj_vxor t (vxor t v) y).mpr hay

namespace CommonHoleConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : CommonHoleConfig p a b c d)
include h

def mirror : CommonHoleConfig (translate p (pair a b)) b a d c where
  outer := h.outer.mirror
  e := h.e
  he := ⟨h.he.2.1,h.he.1,h.he.2.2.2,h.he.2.2.1⟩
  left_eq := h.right_eq
  right_eq := h.left_eq

theorem side_pair (k : Coord) (hk : k∈distinctR a b c d) : InPath p (pair d k) := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  apply (h.outer.left.selected_iff d k (Ne.symm hkd) (Ne.symm h.outer.had)
    (Ne.symm h.outer.hcd) hka hkc).mpr
  rw [h.left_eq]
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
  constructor
  · intro he
    have hm : b∈({d,k}:Finset Coord) := he.symm ▸ (by simp : b∈({b,d}:Finset Coord))
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    exact hm.elim h.outer.hbd (Ne.symm hkb)
  · exact delta_pair_ne d k b h.e (Ne.symm h.outer.hbd) (Ne.symm h.he.2.2.2)

theorem ordinary_b_extension_absent (i j : Coord) (hi : i∈distinctR a b c d)
    (hj : j∈distinctR a b c d) (hij : i≠j) : ¬InPath p (triple b i j) := by
  have hhi := (mem_distinctR a b c d i).mp hi
  have hhj := (mem_distinctR a b c d j).mp hj
  have hs := h.ordinary_corners i j hi hj hij
  by_cases hie : i≠h.e
  · exact middle_row_triple_forbidden p a b i j h.outer.hab (Ne.symm hhi.1)
      (Ne.symm hhj.1) (Ne.symm hhi.2.1) (Ne.symm hhj.2.1) hij
      (h.active_corners i hi hie).1 hs.1 hs.2
  · have hie' : i=h.e := not_ne_iff.mp hie
    have hje : j≠h.e := by intro he; exact hij (hie'.trans he.symm)
    have hs' := h.ordinary_corners j i hj hi (Ne.symm hij)
    have ht := middle_row_triple_forbidden p a b j i h.outer.hab (Ne.symm hhj.1)
      (Ne.symm hhi.1) (Ne.symm hhj.2.1) (Ne.symm hhi.2.1) (Ne.symm hij)
      (h.active_corners j hj hje).1 hs'.1 hs'.2
    simpa only [triple_swap b j i] using ht

theorem missing_ordinary_pair_low (f : MissingAtNeighbor p a b) (i j : Coord)
    (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d) (hij : i≠j)
    (hm : ({i,j}:Finset Coord)∈f.F) : AtMostOneNeighbor p (pair i j) := by
  have hhi := (mem_distinctR a b c d i).mp hi
  have hhj := (mem_distinctR a b c d j).mp hj
  have hs := h.ordinary_corners i j hi hj hij
  have hna : ¬InPath p (triple a i j) := by
    intro ht
    exact (f.selected_iff i j hij hhi.1 hhi.2.1 hhj.1 hhj.2.1).mp ht hm
  have hnb := h.ordinary_b_extension_absent i j hi hj hij
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (pair i j) w) : w=triple i j c := by
    obtain ⟨r,rfl⟩ := neighbor_pair i j hadj
    by_cases hri : r=i
    · subst r; rw [triple_cancel_left] at hw
      exact False.elim (h.outer.absent_unit j hhj.1 hhj.2.2.1 hw)
    by_cases hrj : r=j
    · subst r; rw [triple_cancel_right] at hw
      exact False.elim (h.outer.absent_unit i hhi.1 hhi.2.2.1 hw)
    by_cases hra : r=a
    · subst r; rw [triple_rotate] at hw; exact False.elim (hna hw)
    by_cases hrb : r=b
    · subst r; rw [triple_rotate] at hw; exact False.elim (hnb hw)
    by_cases hrc : r=c
    · subst r; rfl
    by_cases hrd : r=d
    · subst r
      have hdi : InPath p (pair i d) := by simpa only [pair_comm d i] using h.side_pair i hi
      have hdj : InPath p (pair j d) := by simpa only [pair_comm d j] using h.side_pair j hj
      exact False.elim (selected_triple_forbidden p i j d hij hhi.2.2.2 hhj.2.2.2 hs.1 hdi hdj hw)
    have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
    exact False.elim (selected_triple_forbidden p i j r hij (Ne.symm hri) (Ne.symm hrj)
      hs.1 (h.ordinary_corners i r hi hr (Ne.symm hri)).1
      (h.ordinary_corners j r hj hr (Ne.symm hrj)).1 hw)
  intro x y hx hy hax hay
  exact (unique x hx hax).trans (unique y hy hay).symm

theorem missing_ordinary_quad_low (f : MissingAtNeighbor p a b) (i j : Coord)
    (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d) (hij : i≠j)
    (hm : ({i,j}:Finset Coord)∈f.F) : AtMostOneNeighbor p (quad a b i j) := by
  have hi' : i∈distinctR b a d c := by
    have hh := (mem_distinctR a b c d i).mp hi
    exact (mem_distinctR b a d c i).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  have hj' : j∈distinctR b a d c := by
    have hh := (mem_distinctR a b c d j).mp hj
    exact (mem_distinctR b a d c j).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  have hl := h.mirror.missing_ordinary_pair_low f.mirror i j hi' hj' hij hm
  have ht := low_of_translate p (pair a b) (pair i j) hl
  simpa only [quad,triple,pair,vxor_assoc] using ht

end CommonHoleConfig
#print axioms CommonHoleConfig.missing_ordinary_pair_low
#print axioms CommonHoleConfig.missing_ordinary_quad_low
end
end Snake9
