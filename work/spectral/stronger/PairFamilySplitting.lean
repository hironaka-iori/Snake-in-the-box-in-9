import OuterMatchingCount

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

def incidentCoordinates (F : Finset (Finset Coord)) (b : Coord) : Finset Coord :=
  Finset.univ.filter (fun k => k≠b ∧ ({b,k}:Finset Coord)∈F)

def nonincidentEdges (F : Finset (Finset Coord)) (b : Coord) : Finset (Finset Coord) :=
  F.filter (fun s => b∉s)

theorem pair_family_split_card (F : Finset (Finset Coord)) (b : Coord)
    (hedge : ∀s∈F,s.card=2) :
    (incidentCoordinates F b).card+(nonincidentEdges F b).card=F.card := by
  have himage : (incidentCoordinates F b).image (fun k => ({b,k}:Finset Coord)) =
      F.filter (fun s => b∈s) := by
    ext s
    constructor
    · intro hs
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).2.2,by simp⟩
    · intro hs
      obtain ⟨hs,hbs⟩ := Finset.mem_filter.mp hs
      obtain ⟨k,hkb,rfl⟩ := two_element_set_with_member s b (hedge s hs) hbs
      exact Finset.mem_image.mpr ⟨k,by simp [incidentCoordinates,hkb,hs],rfl⟩
  have hinj : Set.InjOn (fun k => ({b,k}:Finset Coord)) (incidentCoordinates F b) := by
    intro i hi j hj he
    change ({b,i}:Finset Coord)={b,j} at he
    have hm : i∈({b,j}:Finset Coord) := he ▸ (by simp)
    simpa [(Finset.mem_filter.mp hi).2.1] using hm
  have hc := Finset.filter_card_add_filter_neg_card_eq_card (s:=F) (p:=fun s => b∈s)
  rw [←himage,Finset.card_image_of_injOn hinj] at hc
  exact hc

theorem pair_family_disjoint_of_card_union (F : Finset (Finset Coord))
    (hF : F.card=2) (hedge : ∀s∈F,s.card=2) (hunion : (F.biUnion id).card=4)
    (s t : Finset Coord) (hs : s∈F) (ht : t∈F) (hst : s≠t) : Disjoint s t := by
  have hsub : ({s,t}:Finset (Finset Coord))⊆F := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hs
    · exact Finset.mem_singleton.mp hq ▸ ht
  have he : ({s,t}:Finset (Finset Coord))=F :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hF,hst])
  have hu : (s∪t).card=4 := by
    rw [←he] at hunion
    simpa using hunion
  have hc := Finset.card_union_add_card_inter s t
  have hsc := hedge s hs
  have htc := hedge t ht
  have hi : (s∩t).card=0 := by omega
  exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hi)

theorem pair_family_matching_of_card_union (F : Finset (Finset Coord))
    (hF : F.card=2) (hedge : ∀s∈F,s.card=2) (hunion : (F.biUnion id).card=4)
    (i j : Coord) (hijF : ({i,j}:Finset Coord)∈F) (k : Coord) (hki : k≠i) (hkj : k≠j) :
    ({i,k}:Finset Coord)∉F ∧ ({j,k}:Finset Coord)∉F := by
  have hneq (r : Coord) (hr : r=i ∨ r=j) : ({i,j}:Finset Coord)≠{r,k} := by
    intro he
    have hk : k∈({i,j}:Finset Coord) := he ▸ (by simp)
    simpa [hki,hkj] using hk
  constructor
  · intro hh
    have hd := pair_family_disjoint_of_card_union F hF hedge hunion {i,j} {i,k} hijF hh (hneq i (Or.inl rfl))
    exact Finset.disjoint_left.mp hd (by simp : i∈({i,j}:Finset Coord)) (by simp)
  · intro hh
    have hd := pair_family_disjoint_of_card_union F hF hedge hunion {i,j} {j,k} hijF hh (hneq j (Or.inr rfl))
    exact Finset.disjoint_left.mp hd (by simp : j∈({i,j}:Finset Coord)) (by simp)

#print axioms pair_family_split_card
#print axioms pair_family_matching_of_card_union
end
end Snake9
