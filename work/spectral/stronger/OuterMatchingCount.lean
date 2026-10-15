import SmallPairFamilies

namespace Snake9
open scoped BigOperators
open Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

/-- An edge in only one outer family can supply a row only through a hole. -/
def holeEdgeResource (H s : Finset Coord) : Finset Coord :=
  if (s ∩ H).Nonempty then s \ H else ∅

theorem holeEdgeResource_card (H s : Finset Coord) (hs : s.card=2) :
    (holeEdgeResource H s).card ≤ 1 := by
  unfold holeEdgeResource
  split_ifs with hh
  · have hi := Finset.one_le_card.mpr hh
    have hc := Finset.card_sdiff_add_card_inter s H
    omega
  · simp

def outerEdgeResources (H : Finset Coord) (G J : Finset (Finset Coord)) : Finset Coord :=
  (G ∩ J).biUnion id ∪ (G \ J).biUnion (holeEdgeResource H) ∪
    (J \ G).biUnion (holeEdgeResource H)

theorem outerEdgeResources_card (H : Finset Coord) (G J : Finset (Finset Coord))
    (hG : ∀s∈G,s.card=2) (hJ : ∀s∈J,s.card=2) :
    (outerEdgeResources H G J).card ≤ G.card+J.card := by
  have hcommon := pair_family_union_card (G∩J) (fun s hs => hG s (Finset.mem_inter.mp hs).1)
  have hleft : ((G\J).biUnion (holeEdgeResource H)).card ≤ (G\J).card := by
    calc
      _ ≤ ∑s∈G\J,(holeEdgeResource H s).card := Finset.card_biUnion_le
      _ ≤ ∑s∈G\J,1 := Finset.sum_le_sum (fun s hs => holeEdgeResource_card H s (hG s (Finset.mem_sdiff.mp hs).1))
      _ = _ := by simp
  have hright : ((J\G).biUnion (holeEdgeResource H)).card ≤ (J\G).card := by
    calc
      _ ≤ ∑s∈J\G,(holeEdgeResource H s).card := Finset.card_biUnion_le
      _ ≤ ∑s∈J\G,1 := Finset.sum_le_sum (fun s hs => holeEdgeResource_card H s (hJ s (Finset.mem_sdiff.mp hs).1))
      _ = _ := by simp
  have hu := Finset.card_union_le ((G∩J).biUnion id) ((G\J).biUnion (holeEdgeResource H))
  have hv := Finset.card_union_le ((G∩J).biUnion id ∪ (G\J).biUnion (holeEdgeResource H)) ((J\G).biUnion (holeEdgeResource H))
  have hcG := Finset.card_sdiff_add_card_inter G J
  have hcJ := Finset.card_sdiff_add_card_inter J G
  rw [Finset.inter_comm J G] at hcJ
  unfold outerEdgeResources
  omega

theorem mem_outerEdgeResources (H : Finset Coord) (G J : Finset (Finset Coord))
    (k l : Coord) (hk : k∉H)
    (he : ((l∈H ∧ ({k,l}:Finset Coord)∈G∪J) ∨
      (l∉H ∧ ({k,l}:Finset Coord)∈G∩J))) :
    k∈outerEdgeResources H G J := by
  have common (hs : ({k,l}:Finset Coord)∈G∩J) : k∈outerEdgeResources H G J := by
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨{k,l},hs,by simp⟩
  by_cases hc : ({k,l}:Finset Coord)∈G∩J
  · exact common hc
  rcases he with ⟨hl,hs⟩ | ⟨_,hs⟩
  · have hr : k∈holeEdgeResource H {k,l} := by
      have ht : (({k,l}:Finset Coord)∩H).Nonempty := ⟨l,Finset.mem_inter.mpr ⟨by simp,hl⟩⟩
      rw [holeEdgeResource,if_pos ht]
      exact Finset.mem_sdiff.mpr ⟨by simp,hk⟩
    rcases Finset.mem_union.mp hs with hg | hj
    · have hn : ({k,l}:Finset Coord)∉J := fun hj => hc (Finset.mem_inter.mpr ⟨hg,hj⟩)
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨{k,l},Finset.mem_sdiff.mpr ⟨hg,hn⟩,hr⟩
    · have hn : ({k,l}:Finset Coord)∉G := fun hg => hc (Finset.mem_inter.mpr ⟨hg,hj⟩)
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨{k,l},Finset.mem_sdiff.mpr ⟨hj,hn⟩,hr⟩
  · exact common hs

/-- The two outer count-two constraints leave exactly two disjoint common edges.
`E` records the active rows that are already forced to be path endpoints. -/
theorem outer_matching_classification (R H E : Finset Coord) (G J : Finset (Finset Coord))
    (hR : R.card=6) (hH : H⊆R) (hE : E⊆R\H) (hEc : E.card≤2)
    (hGc : G.card+H.card=2) (hJc : J.card+H.card=2)
    (hG : ∀s∈G,s.card=2) (hJ : ∀s∈J,s.card=2)
    (hGr : ∀s∈G,s⊆R) (hJr : ∀s∈J,s⊆R)
    (hcover : ∀k∈R\H,k∈E ∨ ∃l : Coord,
      (l∈H ∧ ({k,l}:Finset Coord)∈G∪J) ∨
      (l∉H ∧ ({k,l}:Finset Coord)∈G∩J)) :
    H=∅ ∧ G=J ∧ G.card=2 ∧ (G.biUnion id).card=4 ∧ E=R\G.biUnion id := by
  have hsub : R\H ⊆ E∪outerEdgeResources H G J := by
    intro k hk
    rcases hcover k hk with he | ⟨l,hl⟩
    · exact Finset.mem_union_left _ he
    · exact Finset.mem_union_right _ (mem_outerEdgeResources H G J k l (Finset.mem_sdiff.mp hk).2 hl)
  have hbound := Finset.card_le_card hsub
  have hu := Finset.card_union_le E (outerEdgeResources H G J)
  have hc := outerEdgeResources_card H G J hG hJ
  have hRH : (R\H).card=6-H.card := by rw [Finset.card_sdiff hH,hR]
  have hHc : H.card=0 := by omega
  have hHz : H=∅ := Finset.card_eq_zero.mp hHc
  have hG2 : G.card=2 := by omega
  have hJ2 : J.card=2 := by omega
  have hred : outerEdgeResources H G J=(G∩J).biUnion id := by
    have hz : holeEdgeResource H = fun _ => ∅ := by
      funext s
      simp [hHz,holeEdgeResource]
    ext k
    simp [outerEdgeResources,hz]
  have hcommon := pair_family_union_card (G∩J) (fun s hs => hG s (Finset.mem_inter.mp hs).1)
  have hIle : (G∩J).card≤G.card := Finset.card_le_card Finset.inter_subset_left
  have hI2 : (G∩J).card=2 := by rw [hred] at hu hc hbound; omega
  have hIG : G∩J=G := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hIJ : G∩J=J := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
  have hGJ : G=J := hIG.symm.trans hIJ
  have hC4 : (G.biUnion id).card=4 := by
    rw [hred,hIG] at hbound hu hc
    rw [hIG] at hcommon
    omega
  have hCR : G.biUnion id⊆R := by
    intro k hk
    obtain ⟨s,hs,hks⟩ := Finset.mem_biUnion.mp hk
    exact hGr s hs hks
  have hneed : R\G.biUnion id⊆E := by
    intro k hk
    have hr : k∈R\H := by simpa [hHz] using (Finset.mem_sdiff.mp hk).1
    have hh := hsub hr
    rw [hred,hIG] at hh
    exact (Finset.mem_union.mp hh).resolve_right (Finset.mem_sdiff.mp hk).2
  have hneedc : (R\G.biUnion id).card=2 := by
    rw [Finset.card_sdiff hCR,hR,hC4]
  have hEE : R\G.biUnion id=E := Finset.eq_of_subset_of_card_le hneed (by omega)
  exact ⟨hHz,hGJ,hG2,hC4,hEE.symm⟩

#print axioms outer_matching_classification
end
end Snake9
