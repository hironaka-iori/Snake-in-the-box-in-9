import SharedOuterSwitch
import OrdinaryEndpointSeparation

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem triple_extension_saturation {m : Nat} (p : Snake m) (a s t i j k : Coord)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (ht : InPath p (triple a s t)) (hi : InPath p (quad a s t i))
    (hj : InPath p (quad a s t j)) : ¬InPath p (quad a s t k) :=
  selected_flip_forbidden p (triple a s t) i j k hij hik hjk ht hi hj

namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem central_ladder_impossible
    (htex : InPath p (triple a h.e h.x))
    (htcx : InPath p (triple a c h.x)) (htdx : InPath p (triple a d h.x))
    (hnrow : ¬AtMostOneNeighbor p (pair b h.x))
    (hnex : ¬AtMostOneNeighbor p (triple a h.e h.x))
    (hndx : ¬AtMostOneNeighbor p (triple a d h.x))
    (excover : ∀w,InPath p w → Adj (triple a h.e h.x) w →
      w=quad a b h.e h.x ∨ w=quad a c h.e h.x)
    (dxcover : ∀w,InPath p w → Adj (triple a d h.x) w →
      w=pair d h.x ∨ w=quad a b d h.x ∨ w=quad a c d h.x ∨ w=quad a d h.e h.x) : False := by
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have hq := (force_two_neighbors p (triple a h.e h.x) (quad a b h.e h.x)
    (quad a c h.e h.x) hnex excover).2
  have hbase : InPath p (quad a b h.e h.x) := by
    apply (h.ordinary.right_pair_iff h.e h.x h.he h.hx h.hex).mpr
    rw [h.Beq]
    exact delta_pair_ne_right _ _ _ _ (Ne.symm h.hex) h.hxy
  have hb : InPath p (quad a h.e h.x b) := by
    have heq : quad a h.e h.x b=quad a b h.e h.x := by apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact heq.symm ▸ hbase
  have hc : InPath p (quad a h.e h.x c) := by
    have heq : quad a h.e h.x c=quad a c h.e h.x := by apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact heq.symm ▸ hq
  have hnde0 := triple_extension_saturation p a h.e h.x b c d h.ordinary.outer.hbc
    h.ordinary.outer.hbd h.ordinary.outer.hcd htex hb hc
  have hnde : ¬InPath p (quad a d h.e h.x) := by
    intro hs
    apply hnde0
    have heq : quad a d h.e h.x=quad a h.e h.x d := by apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact heq ▸ hs
  have hcxBase : InPath p (quad a c h.x b) := by
    have heq : quad a c h.x b=quad a b c h.x := by apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact heq.symm ▸ h.ordinary.side_quad h.x h.hx
  have hcxe : InPath p (quad a c h.x h.e) := by simpa only [quad_swap_last a c h.e h.x] using hq
  have hncd0 := triple_extension_saturation p a c h.x b h.e d (Ne.symm he.2.1)
    h.ordinary.outer.hbd he.2.2.2 htcx hcxBase hcxe
  have hncd : ¬InPath p (quad a c d h.x) := by
    intro hs
    apply hncd0
    simpa only [quad_swap_last a c d h.x] using hs
  have hbdx := (force_two_neighbors p (pair b h.x) (triple b h.x c) (triple b h.x d)
    hnrow (h.ordinary.row_cover h.x h.hx)).2
  have hnbd : ¬InPath p (quad a b d h.x) := by
    have hn := ordinary_quad_absent p d a b h.x (Ne.symm h.ordinary.outer.had)
      (Ne.symm h.ordinary.outer.hab) hx.1 (Ne.symm hx.2.1)
      (by have heq : triple a b d=triple d a b := triple_rotate _ _ _
          exact heq ▸ h.ordinary.outer.habd_selected)
      (by have heq : triple a d h.x=triple d a h.x := by apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
          exact heq ▸ htdx)
      (by simpa only [triple_rotate b h.x d] using hbdx)
    intro hs
    apply hn
    have heq : quad a b d h.x=quad d a b h.x := by apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact heq ▸ hs
  apply hndx
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (triple a d h.x) w) : w=pair d h.x := by
    rcases dxcover w hw hadj with he | he | he | he
    · exact he
    · exact False.elim (hnbd (he ▸ hw))
    · exact False.elim (hncd (he ▸ hw))
    · exact False.elim (hnde (he ▸ hw))
  intro x y hx hy hax hay
  exact (unique x hx hax).trans (unique y hy hay).symm

end SharedOuterConfig
#print axioms SharedOuterConfig.central_ladder_impossible
end
end Snake9
