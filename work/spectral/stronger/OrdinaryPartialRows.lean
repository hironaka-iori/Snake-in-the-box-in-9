import OrdinaryRowGeometry

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
namespace OrdinaryOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : OrdinaryOuterConfig p a b c d)
include h

theorem partial_side_saturation (f : MissingAtNeighbor p a b) (k r s : Coord)
    (hk : k∈distinctR a b c d) (hr : r∈distinctR a b c d) (hkr : k≠r)
    (hsa : s≠a) (hsb : s≠b) (hsk : s≠k) (hsr : s≠r)
    (hskF : ({s,k}:Finset Coord)∉f.F) (hkrF : ({k,r}:Finset Coord)∉f.F)
    (hpartner : (({k,r}:Finset Coord)=h.A ∨ ({k,r}:Finset Coord)=h.B) → ({s,r}:Finset Coord)∉f.F) :
    ¬InPath p (quad a k r s) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have hh' := (mem_distinctR a b c d r).mp hr
  have hkrsel := (f.selected_iff k r hkr hh.1 hh.2.1 hh'.1 hh'.2.1).mpr hkrF
  by_cases he : (({k,r}:Finset Coord)=h.A ∨ ({k,r}:Finset Coord)=h.B)
  · have hskSel := (f.selected_iff s k hsk hsa hsb hh.1 hh.2.1).mpr hskF
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
theorem partial_c_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hstar : ({c,k}:Finset Coord)∉f.F)
    (hspokes : ∀r∈distinctR a b c d,r≠k → ({k,r}:Finset Coord)∉f.F)
    (hpartner : ∀r∈distinctR a b c d, (({k,r}:Finset Coord)=h.A ∨ ({k,r}:Finset Coord)=h.B) → ({c,r}:Finset Coord)∉f.F)
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
    exact False.elim (h.absent_pair_a k hka hkb hw)
  by_cases hrk : r=k
  · subst r; rw [quad_cancel_third] at hw
    exact False.elim (h.absent_pair_a c (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hw)
  by_cases hrb : r=b
  · subst r; left; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  by_cases hrd : r=d
  · subst r; right; exact quad_swap_last _ _ _ _
  apply False.elim (h.partial_side_saturation f k r c hk
    ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩) (Ne.symm hrk)
    (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) (Ne.symm hkc) (Ne.symm hrc) hstar
    (hspokes r ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩) hrk)
    (hpartner r ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩)) _)
  have he : quad a c k r=quad a k r c := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  exact he ▸ hw

theorem partial_d_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hstar : ({d,k}:Finset Coord)∉f.F)
    (hspokes : ∀r∈distinctR a b c d,r≠k → ({k,r}:Finset Coord)∉f.F)
    (hpartner : ∀r∈distinctR a b c d, (({k,r}:Finset Coord)=h.A ∨ ({k,r}:Finset Coord)=h.B) → ({d,r}:Finset Coord)∉f.F)
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
    exact False.elim (h.absent_pair_a k hka hkb hw)
  by_cases hrk : r=k
  · subst r; rw [quad_cancel_third] at hw
    exact False.elim (h.absent_pair_a d (Ne.symm h.outer.had) (Ne.symm h.outer.hbd) hw)
  by_cases hrb : r=b
  · subst r
    apply False.elim (hnq _)
    have he : quad a d k b=quad a b d k := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact he ▸ hw
  by_cases hrc : r=c
  · subst r; right; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  apply False.elim (h.partial_side_saturation f k r d hk
    ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩) (Ne.symm hrk)
    (Ne.symm h.outer.had) (Ne.symm h.outer.hbd) (Ne.symm hkd) (Ne.symm hrd) hstar
    (hspokes r ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩) hrk)
    (hpartner r ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩)) _)
  have he : quad a d k r=quad a k r d := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  exact he ▸ hw



end OrdinaryOuterConfig
#print axioms OrdinaryOuterConfig.partial_side_saturation
#print axioms OrdinaryOuterConfig.partial_c_cover
#print axioms OrdinaryOuterConfig.partial_d_cover
end
end Snake9
