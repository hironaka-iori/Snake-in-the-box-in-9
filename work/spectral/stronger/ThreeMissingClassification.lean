import GeneralMissingFamily
import SmallPairFamilies

namespace Snake9
open scoped BigOperators
open Finset Classical
noncomputable section
set_option maxHeartbeats 2000000

def GoodMissingIndex (F : Finset (Finset Coord)) (a b c d i : Coord) : Prop :=
  i≠a ∧ i≠b ∧ i≠c ∧ i≠d ∧ ({b,i} : Finset Coord)∉F ∧
    ∀j : Coord,({i,j} : Finset Coord)∈F→({b,j} : Finset Coord)∉F

theorem three_missing_classification (F : Finset (Finset Coord)) (a b c d : Coord)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (hFcard : F.card=3) (hedge : ∀s∈F,s.card=2)
    (havoid : ∀s∈F,∀k∈s,k≠a ∧ k≠c) :
    (∃ j : Fin 3 → Coord, Function.Injective j ∧ ∀r,GoodMissingIndex F a b c d (j r)) ∨
    (∃u v : Coord,u≠v ∧ GoodMissingIndex F a b c d u ∧ GoodMissingIndex F a b c d v ∧
      PairIsolated F d ∧ PairIsolated F u ∧ PairIsolated F v) := by
  let H := Finset.univ.filter (fun j : Coord => j≠b ∧ ({b,j} : Finset Coord)∈F)
  let G := F.filter (fun s => b∉s)
  let Q := fun s : Finset Coord => if (s∩H).Nonempty then s\H else ∅
  let B := H ∪ G.biUnion Q
  let W : Finset Coord := Finset.univ \ {a,b,c,d}
  let A := W\B
  have memH (j : Coord) : j∈H ↔ j≠b ∧ ({b,j} : Finset Coord)∈F := by simp [H]
  have memG (s : Finset Coord) : s∈G ↔ s∈F ∧ b∉s := by simp [G]
  have himage : H.image (fun j => ({b,j} : Finset Coord)) = F.filter (fun s => b∈s) := by
    ext s
    constructor
    · intro hs
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_filter.mpr ⟨((memH j).mp hj).2,by simp⟩
    · intro hs
      obtain ⟨hs,hbs⟩ := Finset.mem_filter.mp hs
      obtain ⟨j,hjb,rfl⟩ := two_element_set_with_member s b (hedge s hs) hbs
      exact Finset.mem_image.mpr ⟨j,(memH j).mpr ⟨hjb,hs⟩,rfl⟩
  have hinj : Set.InjOn (fun j => ({b,j} : Finset Coord)) H := by
    intro i hi j hj he
    change ({b,i} : Finset Coord)={b,j} at he
    have hm : i∈({b,j} : Finset Coord) := he ▸ (by simp)
    simpa [((memH i).mp hi).1] using hm
  have hcount : H.card+G.card=3 := by
    have hc := Finset.filter_card_add_filter_neg_card_eq_card (s:=F) (p:=fun s => b∈s)
    rw [←himage,Finset.card_image_of_injOn hinj] at hc
    simpa only [G,hFcard] using hc
  have qcard (s : Finset Coord) (hs : s∈G) : (Q s).card≤1 := by
    dsimp [Q]
    split_ifs with hn
    · have hi : 1≤(s∩H).card := Finset.one_le_card.mpr hn
      have he := Finset.card_sdiff_add_card_inter s H
      have hc := hedge s ((memG s).mp hs).1
      omega
    · simp
  have hBbound : B.card≤H.card+∑s∈G,(Q s).card := by
    have hu := Finset.card_union_le H (G.biUnion Q)
    have hb : (G.biUnion Q).card≤∑s∈G,(Q s).card := Finset.card_biUnion_le
    dsimp [B]
    omega
  have hsum : (∑s∈G,(Q s).card)≤G.card := by
    calc
      _ ≤ ∑s∈G,1 := Finset.sum_le_sum qcard
      _ = _ := by simp
  have hB : B.card≤3 := by omega
  have hW : W.card=5 := by
    simp [W,Finset.card_sdiff (Finset.subset_univ _),Coord,hab,hac,had,hbc,hbd,hcd]
  have inB_of_H {i : Coord} (hi : i∈H) : i∈B := Finset.mem_union_left _ hi
  have edge_subset_B (s : Finset Coord) (hs : s∈G) (hh : (s∩H).Nonempty) : s⊆B := by
    intro i hi
    by_cases hiH : i∈H
    · exact inB_of_H hiH
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨s,hs,by simpa only [Q,if_pos hh] using Finset.mem_sdiff.mpr ⟨hi,hiH⟩⟩
  have good (i : Coord) (hi : i∈A) : GoodMissingIndex F a b c d i := by
    obtain ⟨hiW,hiB⟩ := Finset.mem_sdiff.mp hi
    have hi4 : i≠a ∧ i≠b ∧ i≠c ∧ i≠d := by simpa [W] using hiW
    have hnH : i∉H := fun hh => hiB (inB_of_H hh)
    have hbi : ({b,i} : Finset Coord)∉F := fun hh => hnH ((memH i).mpr ⟨hi4.2.1,hh⟩)
    refine ⟨hi4.1,hi4.2.1,hi4.2.2.1,hi4.2.2.2,hbi,?_⟩
    intro j hij hbj
    have hjb : j≠b := by
      intro he
      have hc := hedge {b,j} hbj
      simp [he] at hc
    have hjH : j∈H := (memH j).mpr ⟨hjb,hbj⟩
    have hijG : ({i,j} : Finset Coord)∈G := (memG _).mpr ⟨hij,by simp [Ne.symm hi4.2.1,Ne.symm hjb]⟩
    have hh : (({i,j} : Finset Coord)∩H).Nonempty := ⟨j,Finset.mem_inter.mpr ⟨by simp,hjH⟩⟩
    exact hiB (edge_subset_B {i,j} hijG hh (by simp))
  by_cases hA3 : 3≤A.card
  · left
    obtain ⟨j,hj⟩ := Function.Embedding.exists_of_card_le_finset (show Fintype.card (Fin 3)≤A.card by simpa using hA3)
    exact ⟨j,j.injective,fun r => good (j r) (hj ⟨r,rfl⟩)⟩
  right
  have hsplit : A.card+(W∩B).card=5 := by
    have he := Finset.card_sdiff_add_card_inter W B
    simpa only [A,hW] using he
  have hinter : (W∩B).card≤B.card := Finset.card_le_card Finset.inter_subset_right
  have hA2 : A.card=2 := by omega
  have hB3 : B.card=3 := by omega
  have hBinW : B⊆W := by
    have he : W∩B=B := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    rw [←he]
    exact Finset.inter_subset_left
  have htouch (s : Finset Coord) (hs : s∈G) : (s∩H).Nonempty := by
    by_cases hh : (s∩H).Nonempty
    · exact hh
    have hz : (Q s).card=0 := by simp only [Q,if_neg hh,Finset.card_empty]
    have hstrict : (∑t∈G,(Q t).card)<G.card := by
      have he := Finset.sum_lt_sum qcard (show ∃t∈G,(Q t).card<1 from ⟨s,hs,by omega⟩)
      simpa using he
    omega
  have isolated (i : Coord) (hib : i≠b) (hiB : i∉B) : PairIsolated F i := by
    intro s hs his
    by_cases hbs : b∈s
    · obtain ⟨j,hjb,hsj⟩ := two_element_set_with_member s b (hedge s hs) hbs
      have hij : i=j := by rw [hsj] at his; simpa [hib] using his
      have hjH : j∈H := (memH j).mpr ⟨hjb,by simpa only [hsj] using hs⟩
      exact hiB (hij.symm ▸ inB_of_H hjH)
    · have hsG : s∈G := (memG s).mpr ⟨hs,hbs⟩
      exact hiB (edge_subset_B s hsG (htouch s hsG) his)
  have hdB : d∉B := by
    intro hd
    have hdW := hBinW hd
    simp [W] at hdW
  obtain ⟨u,v,huv,hAuv⟩ := Finset.card_eq_two.mp hA2
  have huA : u∈A := by rw [hAuv]; simp
  have hvA : v∈A := by rw [hAuv]; simp
  have hu := good u huA
  have hv := good v hvA
  exact ⟨u,v,huv,hu,hv,isolated d (Ne.symm hbd) hdB,
    isolated u hu.2.1 (Finset.mem_sdiff.mp huA).2,
    isolated v hv.2.1 (Finset.mem_sdiff.mp hvA).2⟩

#print axioms three_missing_classification
end
end Snake9
