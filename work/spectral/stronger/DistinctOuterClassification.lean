import DistinctOuterResources
import RepeatedOuterMatching
import SingleDeltaExclusion

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem family_eq_insert_of_incident_erase (F : Finset (Finset Coord)) (b d : Coord)
    (hedge : ∀s∈F,s.card=2) (hbd : ({b,d}:Finset Coord)∈F)
    (hz : (incidentCoordinates F b).erase d=∅) :
    F=insert ({b,d}:Finset Coord) (nonincidentEdges F b) := by
  ext s
  constructor
  · intro hs
    by_cases hbs : b∈s
    · obtain ⟨k,hkb,rfl⟩ := two_element_set_with_member s b (hedge s hs) hbs
      have hk : k∈incidentCoordinates F b := by simp [incidentCoordinates,hkb,hs]
      have hkd : k=d := by
        by_contra hn
        have hm := Finset.mem_erase.mpr ⟨hn,hk⟩
        rw [hz] at hm
        exact Finset.not_mem_empty _ hm
      simp [hkd]
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hs,hbs⟩)
  · intro hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hbd
    · exact (Finset.mem_filter.mp hs).1

namespace DistinctOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : DistinctOuterConfig p a b c d)
include h

theorem single_delta_config (hbd : ({b,d}:Finset Coord)∈h.left.F)
    (hac : ({a,c}:Finset Coord)∉h.right.F) : Nonempty (SingleDeltaConfig p a b c d) := by
  obtain ⟨hH,i,j,k,hi,hj,hk,hij,hik,hjk,hG,hJ⟩ := h.one_delta_remainder_shape hbd hac
  have hleft : h.left.F=insert ({b,d}:Finset Coord) h.leftRemainder :=
    family_eq_insert_of_incident_erase h.left.F b d h.left.edge_card hbd (h.incident_left_erase.trans hH)
  have hcn : c∉incidentCoordinates h.right.F a := by simp [incidentCoordinates,hac]
  have hz : incidentCoordinates h.right.F a=∅ := by
    have he := h.incident_right_erase.trans hH
    rwa [Finset.erase_eq_of_not_mem hcn] at he
  have hright : h.right.F=h.rightRemainder :=
    (nonincident_eq_of_no_incident h.right.F a h.right.edge_card hz).symm
  rw [hG] at hleft
  rw [hJ] at hright
  exact ⟨⟨h,i,j,k,(mem_distinctR a b c d i).mp hi,(mem_distinctR a b c d j).mp hj,
    (mem_distinctR a b c d k).mp hk,hij,hik,hjk,hleft,hright⟩⟩

theorem single_delta_impossible (hbd : ({b,d}:Finset Coord)∈h.left.F)
    (hac : ({a,c}:Finset Coord)∉h.right.F)
    (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) : False := by
  obtain ⟨q⟩ := h.single_delta_config hbd hac
  exact q.impossible f hFcard

theorem double_delta_cases (hbd : ({b,d}:Finset Coord)∈h.left.F)
    (hac : ({a,c}:Finset Coord)∈h.right.F) :
    (∃e : Coord,e∈distinctR a b c d ∧
      h.left.F={{b,d},{b,e}} ∧ h.right.F={{a,c},{a,e}}) ∨
    (∃s t : Finset Coord,s.card=2 ∧ t.card=2 ∧
      s⊆insert d (distinctR a b c d) ∧ t⊆insert c (distinctR a b c d) ∧
      b∉s ∧ a∉t ∧ h.left.F=insert {b,d} {s} ∧ h.right.F=insert {a,c} {t}) := by
  by_cases hz : h.holes=∅
  · right
    have hG1 : h.leftRemainder.card=1 := by have he := h.left_count_present hbd; rw [hz] at he; simp at he; omega
    have hJ1 : h.rightRemainder.card=1 := by have he := h.right_count_present hac; rw [hz] at he; simp at he; omega
    obtain ⟨s,hGs⟩ := Finset.card_eq_one.mp hG1
    obtain ⟨t,hJt⟩ := Finset.card_eq_one.mp hJ1
    have hs : s∈h.leftRemainder := by rw [hGs]; simp
    have ht : t∈h.rightRemainder := by rw [hJt]; simp
    have hleft := family_eq_insert_of_incident_erase h.left.F b d h.left.edge_card hbd (h.incident_left_erase.trans hz)
    have hright := family_eq_insert_of_incident_erase h.right.F a c h.right.edge_card hac (h.incident_right_erase.trans hz)
    change h.left.F=insert {b,d} h.leftRemainder at hleft
    change h.right.F=insert {a,c} h.rightRemainder at hright
    rw [hGs] at hleft
    rw [hJt] at hright
    exact ⟨s,t,h.leftRemainder_edge_card s hs,h.rightRemainder_edge_card t ht,
      h.leftRemainder_support s hs,h.rightRemainder_support t ht,
      (Finset.mem_filter.mp hs).2,(Finset.mem_filter.mp ht).2,hleft,hright⟩
  · left
    obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr hz
    have heR := h.holes_subset he
    have hbe := (Finset.mem_filter.mp he).2
    have hae := (h.same_hole e heR).mp hbe
    obtain ⟨hea,heb,hec,hed⟩ := (mem_distinctR a b c d e).mp heR
    have hne0 : ({b,d}:Finset Coord)≠{b,e} := by
      intro heq
      have hm : e∈({b,d}:Finset Coord) := heq ▸ (by simp)
      simpa [heb,hed] using hm
    have hne2 : ({a,c}:Finset Coord)≠{a,e} := by
      intro heq
      have hm : e∈({a,c}:Finset Coord) := heq ▸ (by simp)
      simpa [hea,hec] using hm
    have hleft : h.left.F={{b,d},{b,e}} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact hbd
        · exact Finset.mem_singleton.mp hs ▸ hbe
      · simp [h.left.Fcard,hne0]
    have hright : h.right.F={{a,c},{a,e}} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro s hs
        rcases Finset.mem_insert.mp hs with rfl | hs
        · exact hac
        · exact Finset.mem_singleton.mp hs ▸ hae
      · simp [h.right.Fcard,hne2]
    exact ⟨e,heR,hleft,hright⟩

end DistinctOuterConfig
#print axioms DistinctOuterConfig.single_delta_impossible
#print axioms DistinctOuterConfig.double_delta_cases
end
end Snake9
