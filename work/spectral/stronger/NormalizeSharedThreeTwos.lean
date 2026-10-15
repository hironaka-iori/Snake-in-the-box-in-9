import ThreeTwosRemainingUnequal
import OrdinaryDisjointExclusion
import SharedOuterBase

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section

theorem OrdinaryOuterConfig.shared_config {m : Nat} {p : Snake m} {a b c d : Coord}
    (h : OrdinaryOuterConfig p a b c d) (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) :
    Nonempty (SharedOuterConfig p a b c d) := by
  have hn : ¬Disjoint h.A h.B := fun hh => h.disjoint_impossible f hFcard hh
  obtain ⟨e,heA,heB⟩ := Finset.not_disjoint_iff.mp hn
  obtain ⟨x,hxe,hAx⟩ := two_element_set_with_member h.A e h.Acard heA
  obtain ⟨y,hye,hBy⟩ := two_element_set_with_member h.B e h.Bcard heB
  have hxA : x∈h.A := by rw [hAx]; simp
  have hyB : y∈h.B := by rw [hBy]; simp
  have hxy : x≠y := by intro he; exact h.hne (by rw [hAx,hBy,he])
  exact ⟨⟨h,e,x,y,h.Asub heA,h.Asub hxA,h.Bsub hyB,Ne.symm hxe,Ne.symm hye,hxy,hAx,hBy⟩⟩

structure SharedThreeTwosConfig {m : Nat} (p : Snake m) where
  a : Coord
  b : Coord
  c : Coord
  d : Coord
  shared : SharedOuterConfig p a b c d
  middle : MissingAtNeighbor p a b
  middle_card : middle.F.card=2

theorem DistinctThreeTwosConfig.to_shared {m : Nat} {p : Snake m}
    (h : DistinctThreeTwosConfig p) : Nonempty (SharedThreeTwosConfig p) := by
  obtain ⟨A,B,hA,hB,hAR,hBR,hAB,hleft,hright⟩ :=
    h.outer.remaining_unequal_ordinary_case h.middle h.middle_card
  let oh : OrdinaryOuterConfig p h.a h.b h.c h.d :=
    ⟨h.outer,A,B,hA,hB,hAR,hBR,hAB,hleft,hright⟩
  obtain ⟨sh⟩ := oh.shared_config h.middle h.middle_card
  exact ⟨⟨h.a,h.b,h.c,h.d,sh,h.middle,h.middle_card⟩⟩

theorem normalize_three_twos_to_shared {m : Nat} (p : Snake m) (r : Nat) (hr : r+4≤m)
    (h1 : localAlpha p ⟨r+1,by omega⟩=2)
    (h2 : localAlpha p ⟨r+2,by omega⟩=2)
    (h3 : localAlpha p ⟨r+3,by omega⟩=2) :
    Nonempty (SharedThreeTwosConfig (translate p (p.vertex ⟨r+1,by omega⟩))) := by
  obtain ⟨h⟩ := normalize_three_twos p r hr h1 h2 h3
  exact h.to_shared

#print axioms OrdinaryOuterConfig.shared_config
#print axioms normalize_three_twos_to_shared
end
end Snake9
