import StarLeftGeometry
import RowWindowGeometry

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

structure MixedOuterConfig {m : Nat} (p : Snake m) (a b c d : Coord) where
  left : StarLeftConfig p a b c d
  i : Coord
  j : Coord
  hi : i∈distinctR a b c d
  hj : j∈distinctR a b c d
  hij : i≠j
  right_eq : left.outer.right.F={{a,c},{i,j}}

namespace MixedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : MixedOuterConfig p a b c d)
include h

theorem ordinary_quad (k r : Coord) (hk : k∈distinctR a b c d)
    (hr : r∈distinctR a b c d) (hkr : k≠r)
    (hne : ({k,r}:Finset Coord)≠{h.i,h.j}) : InPath p (quad a b k r) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have hh' := (mem_distinctR a b c d r).mp hr
  apply (h.left.outer.right_pair_iff k r hkr hh.2.1 hh.2.2.2 hh'.2.1 hh'.2.2.2).mpr
  rw [h.right_eq]
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨delta_pair_ne k r a c hh.1 hh.2.2.1,hne⟩

def toLocalDense : LocalDenseRows p a b c d where
  outer := h.left.outer
  rows := distinctR a b c d\{h.i,h.j}
  ordinary_corners := by
    intro k r hkrow hk hr hkr
    refine ⟨h.left.ordinary_pair k r hk hr hkr,h.ordinary_quad k r hk hr hkr ?_⟩
    intro he
    have hnot := (Finset.mem_sdiff.mp hkrow).2
    apply hnot
    rw [←he]
    simp

theorem middle_selected (f : MissingAtNeighbor p a b) (k r : Coord)
    (hk : k∈distinctR a b c d) (hra : r≠a) (hrb : r≠b) (hrk : r≠k)
    (hisol : ∀s∈f.F,k∉s) : InPath p (triple a r k) := by
  have hh := (mem_distinctR a b c d k).mp hk
  apply (f.selected_iff r k hrk hra hrb hh.1 hh.2.1).mpr
  intro hm
  exact hisol _ hm (by simp)

theorem isolated_middle_selected (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s) :
    InPath p (triple a c k) ∧ InPath p (triple a d k) := by
  have hh := (mem_distinctR a b c d k).mp hk
  exact ⟨h.middle_selected f k c hk (Ne.symm h.left.outer.hac)
    (Ne.symm h.left.outer.hbc) (Ne.symm hh.2.2.1) hisol,
    h.middle_selected f k d hk (Ne.symm h.left.outer.had)
    (Ne.symm h.left.outer.hbd) (Ne.symm hh.2.2.2) hisol⟩

theorem isolated_side_saturation (f : MissingAtNeighbor p a b) (k r s : Coord)
    (hk : k∈distinctR a b c d) (hr : r∈distinctR a b c d) (hkr : k≠r)
    (hsa : s≠a) (hsb : s≠b) (hsk : s≠k) (hsr : s≠r)
    (hisol : ∀t∈f.F,k∉t)
    (hpartner : ({k,r}:Finset Coord)={h.i,h.j} → ({s,r}:Finset Coord)∉f.F) :
    ¬InPath p (quad a k r s) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have hh' := (mem_distinctR a b c d r).mp hr
  have hkrsel : InPath p (triple a k r) := by
    simpa only [triple_swap a r k] using
      h.middle_selected f k r hk hh'.1 hh'.2.1 (Ne.symm hkr) hisol
  by_cases he : ({k,r}:Finset Coord)={h.i,h.j}
  · have hskSel := h.middle_selected f k s hk hsa hsb hsk hisol
    have hsrSel := (f.selected_iff s r hsr hsa hsb hh'.1 hh'.2.1).mpr (hpartner he)
    have hbad := ordinary_quad_absent p a s k r (Ne.symm hsa) (Ne.symm hsk)
      (Ne.symm hsr) hkr hskSel hsrSel hkrsel
    intro hx
    apply hbad
    have heq : quad a k r s=quad a s k r := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact heq ▸ hx
  · exact two_layer_saturation p a b k r s h.left.outer.hab hsa hsb
      (h.left.ordinary_pair k r hk hr hkr) (h.ordinary_quad k r hk hr hkr he) hkrsel

end MixedOuterConfig
#print axioms MixedOuterConfig.isolated_side_saturation
end
end Snake9
