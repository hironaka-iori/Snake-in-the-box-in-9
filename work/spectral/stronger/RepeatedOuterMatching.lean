import RepeatedOuterGeometry
import PairFamilySplitting

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem nonincident_eq_of_no_incident (F : Finset (Finset Coord)) (b : Coord)
    (hedge : ∀s∈F,s.card=2) (hz : incidentCoordinates F b=∅) : nonincidentEdges F b=F := by
  apply Finset.filter_eq_self.mpr
  intro s hs hbs
  obtain ⟨k,hkb,rfl⟩ := two_element_set_with_member s b (hedge s hs) hbs
  have hk : k∈incidentCoordinates F b := by simp [incidentCoordinates,hkb,hs]
  rw [hz] at hk
  exact Finset.not_mem_empty _ hk

namespace RepeatedOuterConfig
variable {m : Nat} {p : Snake m} {a b c : Coord} (h : RepeatedOuterConfig p a b c)
include h

theorem outer_matching :
    ∃G : Finset (Finset Coord),∃u v : Coord,
      h.left.F=G ∧ h.right.F=G ∧ G.card=2 ∧ (G.biUnion id).card=4 ∧
      (∀s∈G,s⊆repeatedR a b c) ∧ u≠v ∧ u∈repeatedR a b c ∧ v∈repeatedR a b c ∧
      PairIsolated G u ∧ PairIsolated G v ∧
      InPath p (pair b u) ∧ AtMostOneNeighbor p (pair b u) ∧
      InPath p (pair b v) ∧ AtMostOneNeighbor p (pair b v) := by
  let R := repeatedR a b c
  let H := incidentCoordinates h.left.F b
  let G := nonincidentEdges h.left.F b
  let J := nonincidentEdges h.right.F a
  let E := (R\H).filter (fun k => AtMostOneNeighbor p (pair b k))
  have hR : R.card=6 := by
    simp [R,repeatedR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.hab,h.hac,h.hbc]
  have hHR : H⊆R := by
    intro k hk
    obtain ⟨hkb,hbk⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨hka,hkc⟩ := h.left.avoids {b,k} hbk k (by simp)
    exact (mem_repeatedR a b c k).mpr ⟨hka,hkb,hkc⟩
  have hsame : incidentCoordinates h.right.F a=H := by
    ext k
    constructor
    · intro hk
      obtain ⟨hka,hak⟩ := (Finset.mem_filter.mp hk).2
      obtain ⟨hkb,hkc⟩ := h.right.avoids {a,k} hak k (by simp)
      have hr : k∈repeatedR a b c := (mem_repeatedR a b c k).mpr ⟨hka,hkb,hkc⟩
      have hb := (h.same_hole k hr).mpr hak
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkb,hb⟩
    · intro hk
      have hr := hHR hk
      obtain ⟨hka,hkb,hkc⟩ := (mem_repeatedR a b c k).mp hr
      have hb := (Finset.mem_filter.mp hk).2.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hka,(h.same_hole k hr).mp hb⟩
  have hGc : G.card+H.card=2 := by
    have hc := pair_family_split_card h.left.F b h.left.edge_card
    rw [h.left.Fcard] at hc
    change H.card+G.card=2 at hc
    omega
  have hJc : J.card+H.card=2 := by
    have hc := pair_family_split_card h.right.F a h.right.edge_card
    rw [h.right.Fcard,hsame] at hc
    change H.card+J.card=2 at hc
    omega
  have hG : ∀s∈G,s.card=2 := fun s hs => h.left.edge_card s (Finset.mem_filter.mp hs).1
  have hJ : ∀s∈J,s.card=2 := fun s hs => h.right.edge_card s (Finset.mem_filter.mp hs).1
  have hGr : ∀s∈G,s⊆R := by
    intro s hs k hk
    obtain ⟨hs,hbs⟩ := Finset.mem_filter.mp hs
    obtain ⟨hka,hkc⟩ := h.left.avoids s hs k hk
    exact (mem_repeatedR a b c k).mpr ⟨hka,fun he => hbs (he ▸ hk),hkc⟩
  have hJr : ∀s∈J,s⊆R := by
    intro s hs k hk
    obtain ⟨hs,has⟩ := Finset.mem_filter.mp hs
    obtain ⟨hkb,hkc⟩ := h.right.avoids s hs k hk
    exact (mem_repeatedR a b c k).mpr ⟨fun he => has (he ▸ hk),hkb,hkc⟩
  have selected_row (k : Coord) (hk : k∈R\H) : InPath p (pair b k) := by
    obtain ⟨hr,hn⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨hka,hkb,hkc⟩ := (mem_repeatedR a b c k).mp hr
    apply (h.left.selected_iff b k (Ne.symm hkb) (Ne.symm h.hab) h.hbc hka hkc).mpr
    intro he
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkb,he⟩)
  have hER : E⊆R\H := Finset.filter_subset _ _
  have hEc : E.card≤2 := by
    have hs : E.image (fun k => pair b k)⊆selectedEndpoints p := by
      intro v hv
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,selected_row k (hER hk),(Finset.mem_filter.mp hk).2⟩
    have hc := (Finset.card_le_card hs).trans (selectedEndpoints_card p)
    have hinj : Set.InjOn (fun k => pair b k) E := by
      intro k hk l hl he
      exact pair_injective_right b k l he
    rw [Finset.card_image_of_injOn hinj] at hc
    exact hc
  have cover : ∀k∈R\H,k∈E ∨ ∃l : Coord,
      (l∈H ∧ ({k,l}:Finset Coord)∈G∪J) ∨ (l∉H ∧ ({k,l}:Finset Coord)∈G∩J) := by
    intro k hk
    by_cases hklo : AtMostOneNeighbor p (pair b k)
    · exact Or.inl (Finset.mem_filter.mpr ⟨hk,hklo⟩)
    right
    obtain ⟨w,hw,hadj,hwn⟩ := neighbor_other_of_not_low p (pair b k) (triple b k c) hklo
    rcases h.row_neighbor_cover k (Finset.mem_sdiff.mp hk).1 w hw hadj with he | ⟨l,hl,hlk,rfl⟩
    · exact False.elim (hwn he)
    obtain ⟨hka,hkb,hkc⟩ := (mem_repeatedR a b c k).mp (Finset.mem_sdiff.mp hk).1
    obtain ⟨hla,hlb,hlc⟩ := (mem_repeatedR a b c l).mp hl
    have hc := h.row_connection_missing k l (Finset.mem_sdiff.mp hk).1 hl (Ne.symm hlk) (selected_row k hk) hw
    have left_mem (he : ({k,l}:Finset Coord)∈h.left.F) : ({k,l}:Finset Coord)∈G := by
      exact Finset.mem_filter.mpr ⟨he,by simp [Ne.symm hkb,Ne.symm hlb]⟩
    have right_mem (he : ({k,l}:Finset Coord)∈h.right.F) : ({k,l}:Finset Coord)∈J := by
      exact Finset.mem_filter.mpr ⟨he,by simp [Ne.symm hka,Ne.symm hla]⟩
    by_cases hlH : l∈H
    · refine ⟨l,Or.inl ⟨hlH,?_⟩⟩
      rcases hc.1 with he | he
      · exact Finset.mem_union_left _ (left_mem he)
      · exact Finset.mem_union_right _ (right_mem he)
    · have hb := hc.2 (selected_row l (Finset.mem_sdiff.mpr ⟨hl,hlH⟩))
      exact ⟨l,Or.inr ⟨hlH,Finset.mem_inter.mpr ⟨left_mem hb.1,right_mem hb.2⟩⟩⟩
  obtain ⟨hHz,hGJ,hG2,hC4,hEeq⟩ := outer_matching_classification R H E G J
    hR hHR hER hEc hGc hJc hG hJ hGr hJr cover
  have hleft : h.left.F=G := (nonincident_eq_of_no_incident h.left.F b h.left.edge_card hHz).symm
  have hright : h.right.F=G := by
    have hh : incidentCoordinates h.right.F a=∅ := hsame.trans hHz
    exact (nonincident_eq_of_no_incident h.right.F a h.right.edge_card hh).symm.trans hGJ.symm
  have hCR : G.biUnion id⊆R := by
    intro k hk
    obtain ⟨s,hs,hks⟩ := Finset.mem_biUnion.mp hk
    exact hGr s hs hks
  have hE2 : E.card=2 := by rw [hEeq,Finset.card_sdiff hCR,hR,hC4]
  obtain ⟨u,v,huv,hEuv⟩ := Finset.card_eq_two.mp hE2
  have huE : u∈E := by rw [hEuv]; simp
  have hvE : v∈E := by rw [hEuv]; simp
  have isolated (k : Coord) (hk : k∈E) : PairIsolated G k := by
    rw [hEeq] at hk
    intro s hs hks
    exact (Finset.mem_sdiff.mp hk).2 (Finset.mem_biUnion.mpr ⟨s,hs,hks⟩)
  exact ⟨G,u,v,hleft,hright,hG2,hC4,hGr,huv,(Finset.mem_sdiff.mp (hER huE)).1,
    (Finset.mem_sdiff.mp (hER hvE)).1,isolated u huE,isolated v hvE,
    selected_row u (hER huE),(Finset.mem_filter.mp huE).2,
    selected_row v (hER hvE),(Finset.mem_filter.mp hvE).2⟩

end RepeatedOuterConfig

#print axioms RepeatedOuterConfig.outer_matching
end
end Snake9
