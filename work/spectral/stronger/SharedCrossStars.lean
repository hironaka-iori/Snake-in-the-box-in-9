import SharedCoreEndpoints
import OrdinaryMissingStar

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 2000000
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem cx_dy_false (f : MissingAtNeighbor p a b) (hF : f.F={{c,h.x},{d,h.y}}) : False := by
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have hy := (mem_distinctR a b c d h.y).mp h.hy
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hsupp : ∀s∈f.F,s⊆{c,d,h.e,h.x,h.y} := by
    intro s hs
    rw [hF] at hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simp [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    · rw [Finset.mem_singleton.mp hs]
      simp [Finset.insert_subset_iff,Finset.singleton_subset_iff]
  have hyA : h.y∉h.ordinary.A := by simp [h.Aeq,Ne.symm h.hey,Ne.symm h.hxy]
  have hck : ({c,h.y}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne_right _ _ _ _ hy.2.2.1 (Ne.symm h.hxy),
      delta_pair_ne _ _ _ _ h.ordinary.outer.hcd (Ne.symm hy.2.2.1)⟩
  have hdk : ({d,h.y}:Finset Coord)∈f.F := by rw [hF]; simp
  have hcd : ({c,d}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne_right _ _ _ _ (Ne.symm h.ordinary.outer.hcd) (Ne.symm hx.2.2.2),
      delta_pair_ne _ _ _ _ h.ordinary.outer.hcd (Ne.symm hy.2.2.1)⟩
  have hce : ({c,h.e}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne_right _ _ _ _ he.2.2.1 h.hex,
      delta_pair_ne _ _ _ _ h.ordinary.outer.hcd (Ne.symm hy.2.2.1)⟩
  have hspokes : ∀r∈distinctR a b c d,r≠h.y → ({h.y,r}:Finset Coord)∉f.F := by
    intro r hr hry
    have hh := (mem_distinctR a b c d r).mp hr
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ hy.2.2.1 (Ne.symm h.hxy),
      delta_pair_ne_right _ _ _ _ hh.2.2.2 hry⟩
  have hpartner : ∀r∈distinctR a b c d,
      (({h.y,r}:Finset Coord)=h.ordinary.A ∨ ({h.y,r}:Finset Coord)=h.ordinary.B) → ({c,r}:Finset Coord)∉f.F := by
    intro r hr hh
    rcases hh with hh | hh
    · exact False.elim (hyA (hh ▸ (by simp : h.y∈({h.y,r}:Finset Coord))))
    · rw [h.Beq] at hh
      have hr' : r=h.e := by
        have hm : h.e∈({h.y,r}:Finset Coord) := hh.symm ▸ (by simp)
        simpa [h.hey,eq_comm] using hm
      simpa only [hr'] using hce
  have htc := (f.selected_iff c h.y (Ne.symm hy.2.2.1) (Ne.symm h.ordinary.outer.hac)
    (Ne.symm h.ordinary.outer.hbc) hy.1 hy.2.1).mpr hck
  rcases h.ordinary.missing_d_row_endpoint f h.y h.hy hyA hck hdk hcd hspokes hpartner with hl | hl | hl
  · apply h.core_internal f hsupp _ (h.ordinary.row_selected h.y h.hy) _ hl
    intro k hk hke hkx hky
    have hh := (mem_distinctR a b c d k).mp hk
    simp [bit_pair,Ne.symm hh.2.1,Ne.symm hky]
  · apply h.core_internal f hsupp _ htc _ hl
    intro k hk hke hkx hky
    have hh := (mem_distinctR a b c d k).mp hk
    simp [bit_triple,Ne.symm hh.1,Ne.symm hh.2.2.1,Ne.symm hky]
  · apply h.core_internal f hsupp _ (h.ordinary.side_pair h.y h.hy) _ hl
    intro k hk hke hkx hky
    have hh := (mem_distinctR a b c d k).mp hk
    simp [bit_pair,Ne.symm hh.2.2.2,Ne.symm hky]

end SharedOuterConfig
#print axioms SharedOuterConfig.cx_dy_false
end
end Snake9
