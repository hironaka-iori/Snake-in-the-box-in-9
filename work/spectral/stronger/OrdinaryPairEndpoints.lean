import OrdinaryRowGeometry
import CommonHolePairs

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
namespace OrdinaryOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : OrdinaryOuterConfig p a b c d)
include h

theorem left_clean_pair (i j : Coord) (hi : i∈distinctR a b c d)
    (hj : j∈distinctR a b c d) (hij : i≠j) (hiA : i∉h.A) : InPath p (pair i j) := by
  apply (h.left_pair_iff i j hi hj hij).mpr
  intro he
  exact hiA (he ▸ (by simp : i∈({i,j}:Finset Coord)))

theorem missing_ordinary_pair_low (f : MissingAtNeighbor p a b) (i j : Coord)
    (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d) (hij : i≠j)
    (hiA : i∉h.A) (hjA : j∉h.A)
    (hm : ({i,j}:Finset Coord)∈f.F) : AtMostOneNeighbor p (pair i j) := by
  have hhi := (mem_distinctR a b c d i).mp hi
  have hhj := (mem_distinctR a b c d j).mp hj
  have hs := h.left_clean_pair i j hi hj hij hiA
  have hna : ¬InPath p (triple a i j) := by
    intro ht
    exact (f.selected_iff i j hij hhi.1 hhi.2.1 hhj.1 hhj.2.1).mp ht hm
  have hnb := h.ordinary_b_absent i j hi hj hij
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
      exact False.elim (selected_triple_forbidden p i j d hij hhi.2.2.2 hhj.2.2.2 hs hdi hdj hw)
    have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
    exact False.elim (selected_triple_forbidden p i j r hij (Ne.symm hri) (Ne.symm hrj)
      hs (h.left_clean_pair i r hi hr (Ne.symm hri) hiA)
      (h.left_clean_pair j r hj hr (Ne.symm hrj) hjA) hw)
  intro x y hx hy hax hay
  exact (unique x hx hax).trans (unique y hy hay).symm

theorem missing_ordinary_quad_low (f : MissingAtNeighbor p a b) (i j : Coord)
    (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d) (hij : i≠j)
    (hiB : i∉h.B) (hjB : j∉h.B)
    (hm : ({i,j}:Finset Coord)∈f.F) : AtMostOneNeighbor p (quad a b i j) := by
  have hi' : i∈distinctR b a d c := by
    have hh := (mem_distinctR a b c d i).mp hi
    exact (mem_distinctR b a d c i).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  have hj' : j∈distinctR b a d c := by
    have hh := (mem_distinctR a b c d j).mp hj
    exact (mem_distinctR b a d c j).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  have hl := h.mirror.missing_ordinary_pair_low f.mirror i j hi' hj' hij hiB hjB hm
  have ht := low_of_translate p (pair a b) (pair i j) hl
  simpa only [quad,triple,pair,vxor_assoc] using ht

end OrdinaryOuterConfig
#print axioms OrdinaryOuterConfig.missing_ordinary_pair_low
#print axioms OrdinaryOuterConfig.missing_ordinary_quad_low
end
end Snake9
