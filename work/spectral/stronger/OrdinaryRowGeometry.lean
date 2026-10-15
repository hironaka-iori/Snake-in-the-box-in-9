import OrdinaryOuterBase
import RowWindowGeometry

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
namespace OrdinaryOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : OrdinaryOuterConfig p a b c d)
include h

theorem ordinary_b_absent (k r : Coord) (hk : k∈distinctR a b c d)
    (hr : r∈distinctR a b c d) (hkr : k≠r) : ¬InPath p (triple b k r) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have hh' := (mem_distinctR a b c d r).mp hr
  by_cases he : ({k,r}:Finset Coord)=h.A
  · have hne : ({k,r}:Finset Coord)≠h.B := by rw [he]; exact h.hne
    have hq := (h.right_pair_iff k r hk hr hkr).mpr hne
    intro hv
    have hkSel : InPath p (SquareIncidence.flip k (triple b k r)) := by
      change InPath p (quad b k r k)
      rw [quad_cancel_second]
      exact h.row_selected r hr
    have hrSel : InPath p (SquareIncidence.flip r (triple b k r)) := by
      change InPath p (quad b k r r)
      rw [quad_cancel_third]
      exact h.row_selected k hk
    apply selected_flip_forbidden p (triple b k r) k r a hkr hh.1 hh'.1 hv hkSel hrSel
    have heq : SquareIncidence.flip a (triple b k r)=quad a b k r := by
      apply Fin.ext; dsimp [SquareIncidence.flip,quad,triple,pair,vxor]; ac_rfl
    exact heq.symm ▸ hq
  · exact selected_triple_forbidden p b k r (Ne.symm hh.2.1) (Ne.symm hh'.2.1) hkr
      (h.row_selected k hk) (h.row_selected r hr) ((h.left_pair_iff k r hk hr hkr).mpr he)

theorem row_cover (k : Coord) (hk : k∈distinctR a b c d) :
    ∀w,InPath p w → Adj (pair b k) w → w=triple b k c ∨ w=triple b k d := by
  intro w hw hadj
  rcases h.outer.row_neighbor_cover k hk w hw hadj with he | he | ⟨l,hl,hlk,he⟩
  · exact Or.inl he
  · exact Or.inr he
  · exact False.elim (h.ordinary_b_absent k l hk hl (Ne.symm hlk) (he ▸ hw))

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
  exact ⟨h.middle_selected f k c hk (Ne.symm h.outer.hac)
    (Ne.symm h.outer.hbc) (Ne.symm hh.2.2.1) hisol,
    h.middle_selected f k d hk (Ne.symm h.outer.had)
    (Ne.symm h.outer.hbd) (Ne.symm hh.2.2.2) hisol⟩

theorem isolated_side_saturation (f : MissingAtNeighbor p a b) (k r s : Coord)
    (hk : k∈distinctR a b c d) (hr : r∈distinctR a b c d) (hkr : k≠r)
    (hsa : s≠a) (hsb : s≠b) (hsk : s≠k) (hsr : s≠r)
    (hisol : ∀t∈f.F,k∉t)
    (hpartner : (({k,r}:Finset Coord)=h.A ∨ ({k,r}:Finset Coord)=h.B) → ({s,r}:Finset Coord)∉f.F) :
    ¬InPath p (quad a k r s) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have hh' := (mem_distinctR a b c d r).mp hr
  have hkrsel : InPath p (triple a k r) := by
    simpa only [triple_swap a r k] using
      h.middle_selected f k r hk hh'.1 hh'.2.1 (Ne.symm hkr) hisol
  by_cases he : (({k,r}:Finset Coord)=h.A ∨ ({k,r}:Finset Coord)=h.B)
  · have hskSel := h.middle_selected f k s hk hsa hsb hsk hisol
    have hsrSel := (f.selected_iff s r hsr hsa hsb hh'.1 hh'.2.1).mpr (hpartner he)
    have hbad := ordinary_quad_absent p a s k r (Ne.symm hsa) (Ne.symm hsk)
      (Ne.symm hsr) hkr hskSel hsrSel hkrsel
    intro hx
    apply hbad
    have heq : quad a k r s=quad a s k r := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact heq ▸ hx
  · exact two_layer_saturation p a b k r s h.outer.hab hsa hsb
      ((h.left_pair_iff k r hk hr hkr).mpr (fun hh => he (Or.inl hh)))
      ((h.right_pair_iff k r hk hr hkr).mpr (fun hh => he (Or.inr hh))) hkrsel

end OrdinaryOuterConfig
#print axioms OrdinaryOuterConfig.ordinary_b_absent
#print axioms OrdinaryOuterConfig.isolated_side_saturation
end
end Snake9
