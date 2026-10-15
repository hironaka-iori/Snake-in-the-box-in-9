import MixedOuterBase

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
namespace MixedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : MixedOuterConfig p a b c d)
include h

theorem isolated_c_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s)
    (hpartner : ∀r∈distinctR a b c d, ({k,r}:Finset Coord)={h.i,h.j} → ({c,r}:Finset Coord)∉f.F)
    (hnc : ¬InPath p (pair c k)) :
    ∀w, InPath p w → Adj (triple a c k) w →
      w=quad a b c k ∨ w=quad a c d k := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_triple a c k hadj
  by_cases hra : r=a
  · subst r; rw [quad_cancel_first] at hw; exact False.elim (hnc hw)
  by_cases hrc : r=c
  · subst r; rw [quad_cancel_second] at hw
    exact False.elim (h.toLocalDense.absent_middle_pair k hka hkb hw)
  by_cases hrk : r=k
  · subst r; rw [quad_cancel_third] at hw
    exact False.elim (h.toLocalDense.absent_middle_pair c (Ne.symm h.left.outer.hac) (Ne.symm h.left.outer.hbc) hw)
  by_cases hrb : r=b
  · subst r; left; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  by_cases hrd : r=d
  · subst r; right; exact quad_swap_last _ _ _ _
  apply False.elim (h.isolated_side_saturation f k r c hk
    ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩) (Ne.symm hrk)
    (Ne.symm h.left.outer.hac) (Ne.symm h.left.outer.hbc) (Ne.symm hkc) (Ne.symm hrc) hisol
    (hpartner r ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩)) _)
  have he : quad a c k r=quad a k r c := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  exact he ▸ hw

theorem isolated_d_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s)
    (hpartner : ∀r∈distinctR a b c d, ({k,r}:Finset Coord)={h.i,h.j} → ({d,r}:Finset Coord)∉f.F)
    (hnq : ¬InPath p (quad a b d k)) :
    ∀w, InPath p w → Adj (triple a d k) w →
      w=pair d k ∨ w=quad a c d k := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_triple a d k hadj
  by_cases hra : r=a
  · subst r; left; exact quad_cancel_first _ _ _
  by_cases hrd : r=d
  · subst r; rw [quad_cancel_second] at hw
    exact False.elim (h.toLocalDense.absent_middle_pair k hka hkb hw)
  by_cases hrk : r=k
  · subst r; rw [quad_cancel_third] at hw
    exact False.elim (h.toLocalDense.absent_middle_pair d (Ne.symm h.left.outer.had) (Ne.symm h.left.outer.hbd) hw)
  by_cases hrb : r=b
  · subst r
    apply False.elim (hnq _)
    have he : quad a d k b=quad a b d k := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact he ▸ hw
  by_cases hrc : r=c
  · subst r; right; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  apply False.elim (h.isolated_side_saturation f k r d hk
    ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩) (Ne.symm hrk)
    (Ne.symm h.left.outer.had) (Ne.symm h.left.outer.hbd) (Ne.symm hkd) (Ne.symm hrd) hisol
    (hpartner r ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩)) _)
  have he : quad a d k r=quad a k r d := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  exact he ▸ hw


theorem isolated_endpoint_group_of_partners (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s)
    (hC : ∀r∈distinctR a b c d, ({k,r}:Finset Coord)={h.i,h.j} → ({c,r}:Finset Coord)∉f.F)
    (hD : ∀r∈distinctR a b c d, ({k,r}:Finset Coord)={h.i,h.j} → ({d,r}:Finset Coord)∉f.F) :
    AtMostOneNeighbor p (pair b k) ∨ AtMostOneNeighbor p (triple a c k) ∨
      AtMostOneNeighbor p (triple a d k) := by
  exact row_window_endpoint_group h.left.outer k hk (h.left.row_selected k hk)
    (h.isolated_middle_selected f k hk hisol) (h.left.row_cover k hk)
    (h.isolated_c_cover f k hk hisol hC) (h.isolated_d_cover f k hk hisol hD)

end MixedOuterConfig
#print axioms MixedOuterConfig.isolated_endpoint_group_of_partners
end
end Snake9
