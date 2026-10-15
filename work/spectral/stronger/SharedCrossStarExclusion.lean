import SharedCrossMissingStar

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 2000000
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem two_indices_avoiding (r : Coord) (hr : r∈distinctR a b c d)
    (hrx : r≠h.x) (hry : r≠h.y) :
    ∃u v : Coord,u≠v ∧ u∈distinctR a b c d ∧ u≠r ∧ u≠h.x ∧ u≠h.y ∧
      v∈distinctR a b c d ∧ v≠r ∧ v≠h.x ∧ v≠h.y := by
  have hsub : ({r,h.x,h.y}:Finset Coord)⊆distinctR a b c d := by
    intro k hk
    simp only [mem_insert,mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact hr
    · exact h.hx
    · exact h.hy
  have hR : (distinctR a b c d).card=5 := by
    simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.ordinary.outer.hab,
      h.ordinary.outer.hac,h.ordinary.outer.had,h.ordinary.outer.hbc,h.ordinary.outer.hbd,h.ordinary.outer.hcd]
  have hc : (distinctR a b c d\{r,h.x,h.y}).card=2 := by
    rw [Finset.card_sdiff hsub,hR]
    simp [hrx,hry,h.hxy]
  obtain ⟨u,v,huv,heq⟩ := Finset.card_eq_two.mp hc
  have hu : u∈distinctR a b c d\{r,h.x,h.y} := by rw [heq]; simp
  have hv : v∈distinctR a b c d\{r,h.x,h.y} := by rw [heq]; simp
  simp only [mem_sdiff,mem_insert,mem_singleton,not_or] at hu hv
  exact ⟨u,v,huv,hu.1,hu.2.1,hu.2.2.1,hu.2.2.2,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2⟩

theorem dr_xy_false (f : MissingAtNeighbor p a b) (r : Coord)
    (hr : r∈distinctR a b c d) (hrx : r≠h.x) (hry : r≠h.y)
    (hF : f.F={{d,r},{h.x,h.y}}) : False := by
  have hh := (mem_distinctR a b c d r).mp hr
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have hy := (mem_distinctR a b c d h.y).mp h.hy
  have hcstar (s : Coord) (hs : s∈distinctR a b c d) : ({c,s}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ h.ordinary.outer.hcd (Ne.symm hh.2.2.1),
      delta_pair_ne _ _ _ _ (Ne.symm hx.2.2.1) (Ne.symm hy.2.2.1)⟩
  have hcd : ({c,d}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ h.ordinary.outer.hcd (Ne.symm hh.2.2.1),
      delta_pair_ne _ _ _ _ (Ne.symm hx.2.2.1) (Ne.symm hy.2.2.1)⟩
  have hdx : ({d,h.x}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne_right _ _ _ _ hx.2.2.2 (Ne.symm hrx),
      delta_pair_ne _ _ _ _ (Ne.symm hx.2.2.2) (Ne.symm hy.2.2.2)⟩
  have hspokes (s : Coord) (hs : s∈distinctR a b c d) (hsx : s≠h.x) (hsy : s≠h.y) :
      ({h.x,s}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ hx.2.2.2 (Ne.symm hrx),
      delta_pair_ne_right _ _ _ _ hsx hsy⟩
  have good (k : Coord) (hk : k∈distinctR a b c d) (hkr : k≠r) (hkx : k≠h.x) (hky : k≠h.y) :
      OrdinaryGoodRow f.F (distinctR a b c d) h.ordinary.A h.ordinary.B c d k := by
    refine ⟨?_,Or.inr ⟨hcd,Or.inl ?_⟩⟩
    · have hh := (mem_distinctR a b c d k).mp hk
      rw [hF]
      intro s hs
      simp only [mem_insert,mem_singleton] at hs
      rcases hs with rfl | rfl <;> simp [hh.2.2.2,hkr,hkx,hky]
    · intro s hs _
      exact hcstar s hs
  obtain ⟨u,v,huv,hu,hur,hux,huy,hv,hvr,hvx,hvy⟩ := h.two_indices_avoiding r hr hrx hry
  exact h.cross_c_two_rows_false f (by rw [hF]; simp) hcstar hcd hdx hspokes
    u v hu hv huv hux huy hvx hvy (good u hu hur hux huy) (good v hv hvr hvx hvy)

theorem cr_xy_false (f : MissingAtNeighbor p a b) (r : Coord)
    (hr : r∈distinctR a b c d) (hrx : r≠h.x) (hry : r≠h.y)
    (hF : f.F={{c,r},{h.x,h.y}}) : False := by
  have hh := (mem_distinctR a b c d r).mp hr
  have hrm := (mem_distinctR b a d c r).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  apply h.mirror.dr_xy_false f.mirror r hrm hry hrx
  change f.F={{c,r},{h.y,h.x}}
  simpa only [Finset.pair_comm h.y h.x] using hF

end SharedOuterConfig
#print axioms SharedOuterConfig.dr_xy_false
#print axioms SharedOuterConfig.cr_xy_false
end
end Snake9
