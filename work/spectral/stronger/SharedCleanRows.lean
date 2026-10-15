import SharedOuterBase
import OrdinaryTwoEndpoints

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1500000
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem two_clean_indices : ∃u v : Coord,u≠v ∧
    u∈distinctR a b c d ∧ u≠h.e ∧ u≠h.x ∧ u≠h.y ∧
    v∈distinctR a b c d ∧ v≠h.e ∧ v≠h.x ∧ v≠h.y := by
  have hsub : ({h.e,h.x,h.y}:Finset Coord)⊆distinctR a b c d := by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact h.he
    · exact h.hx
    · exact h.hy
  have hR : (distinctR a b c d).card=5 := by
    simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.ordinary.outer.hab,
      h.ordinary.outer.hac,h.ordinary.outer.had,h.ordinary.outer.hbc,
      h.ordinary.outer.hbd,h.ordinary.outer.hcd]
  have hc : (distinctR a b c d\{h.e,h.x,h.y}).card=2 := by
    rw [Finset.card_sdiff hsub,hR]
    simp [h.hex,h.hey,h.hxy]
  obtain ⟨u,v,huv,heq⟩ := Finset.card_eq_two.mp hc
  have hu : u∈distinctR a b c d\{h.e,h.x,h.y} := by rw [heq]; simp
  have hv : v∈distinctR a b c d\{h.e,h.x,h.y} := by rw [heq]; simp
  simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,not_or] at hu hv
  exact ⟨u,v,huv,hu.1,hu.2.1,hu.2.2.1,hu.2.2.2,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2⟩

theorem clean_isolated_good (f : MissingAtNeighbor p a b) (u : Coord)
    (hu : u∈distinctR a b c d) (hue : u≠h.e) (hux : u≠h.x) (huy : u≠h.y)
    (his : ∀s∈f.F,u∉s) :
    OrdinaryGoodRow f.F (distinctR a b c d) h.ordinary.A h.ordinary.B c d u := by
  refine ⟨his,Or.inl ⟨?_,?_⟩⟩
  all_goals
    intro r hr hhole
    rcases hhole with hA | hB
    · rw [h.Aeq] at hA
      exact False.elim (delta_pair_ne u r h.e h.x hue hux hA)
    · rw [h.Beq] at hB
      exact False.elim (delta_pair_ne u r h.e h.y hue huy hB)

end SharedOuterConfig
#print axioms SharedOuterConfig.two_clean_indices
#print axioms SharedOuterConfig.clean_isolated_good
end
end Snake9
