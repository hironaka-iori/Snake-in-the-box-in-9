import EndpointMissingConfig
import OneTwoDispatch

namespace Snake9
open scoped BigOperators
open Finset Classical
noncomputable section
set_option maxHeartbeats 1500000

def PairIsolated (F : Finset (Finset Coord)) (k : Coord) : Prop :=
  ∀ s∈F, k∉s

theorem pair_family_union_card (F : Finset (Finset Coord))
    (hedge : ∀s∈F,s.card=2) : (F.biUnion id).card ≤ 2*F.card := by
  calc
    _ ≤ ∑ s∈F,s.card := Finset.card_biUnion_le
    _ = F.card*2 := Finset.sum_const_nat hedge
    _ = _ := Nat.mul_comm _ _

theorem pair_family_overlap_bound (F : Finset (Finset Coord))
    (hcard : F.card≤3) (hedge : ∀s∈F,s.card=2)
    (s t : Finset Coord) (hs : s∈F) (ht : t∈F) (hst : s≠t)
    (u : Coord) (hus : u∈s) (hut : u∈t) : (F.biUnion id).card≤5 := by
  let R := F \ {s,t}
  have hsub : ({s,t} : Finset (Finset Coord)) ⊆ F := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hs
    · simpa only [Finset.mem_singleton.mp he] using ht
  have hR : R.card≤1 := by
    dsimp [R]
    rw [Finset.card_sdiff hsub]
    have hstc : ({s,t} : Finset (Finset Coord)).card=2 := by simp [hst]
    rw [hstc]
    omega
  have hRc : (R.biUnion id).card≤2 := by
    have hc := pair_family_union_card R (fun x hx => hedge x (Finset.mem_sdiff.mp hx).1)
    omega
  have hint : 1≤(s∩t).card := Finset.one_le_card.mpr ⟨u,Finset.mem_inter.mpr ⟨hus,hut⟩⟩
  have heq := Finset.card_union_add_card_inter s t
  have hsc := hedge s hs
  have htc := hedge t ht
  have hstc : (s∪t).card≤3 := by omega
  have hcover : F.biUnion id ⊆ (s∪t) ∪ R.biUnion id := by
    intro k hk
    obtain ⟨e,he,hk⟩ := Finset.mem_biUnion.mp hk
    by_cases hes : e=s
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hes ▸ hk))
    by_cases het : e=t
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (het ▸ hk))
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨e,Finset.mem_sdiff.mpr ⟨he,by simp [hes,het]⟩,hk⟩
  have hle := Finset.card_le_card hcover
  have hunion := Finset.card_union_le (s∪t) (R.biUnion id)
  omega

theorem small_pair_family_cases (F : Finset (Finset Coord)) (a : Coord)
    (hcard : F.card≤3) (hedge : ∀s∈F,s.card=2)
    (havoid : ∀s∈F,∀k∈s,k≠a) :
    (∃ j : Fin 3 → Coord, Function.Injective j ∧
      ∀r, j r≠a ∧ PairIsolated F (j r)) ∨
    (∃ u v : Coord, u≠a ∧ v≠a ∧ u≠v ∧ PairIsolated F u ∧ PairIsolated F v ∧
      ∀t : Coord,t≠a→t≠u→t≠v→
        ∃j : Coord,j≠a ∧ j≠u ∧ j≠v ∧ j≠t ∧
          ∀k : Coord,({t,k} : Finset Coord)∈F→k=j) := by
  let C := F.biUnion id
  let A := Finset.univ \ insert a C
  have hC : C.card≤6 := by
    have hc := pair_family_union_card F hedge
    change (F.biUnion id).card≤6
    omega
  have haC : a∉C := by
    intro hm
    obtain ⟨s,hs,ha⟩ := Finset.mem_biUnion.mp hm
    exact havoid s hs a ha rfl
  have hAc : A.card = 9-(C.card+1) := by
    simp [A,Finset.card_sdiff (Finset.subset_univ (insert a C)),Finset.card_insert_of_not_mem haC,Coord]
  have hAlarge : 2≤A.card := by omega
  have hAprop (k : Coord) (hk : k∈A) : k≠a ∧ PairIsolated F k := by
    have hm : k≠a ∧ k∉C := by simpa [A] using hk
    refine ⟨hm.1,?_⟩
    intro s hs hks
    exact hm.2 (Finset.mem_biUnion.mpr ⟨s,hs,hks⟩)
  by_cases hA3 : 3≤A.card
  · left
    obtain ⟨j,hj⟩ := Function.Embedding.exists_of_card_le_finset (show Fintype.card (Fin 3)≤A.card by simpa using hA3)
    exact ⟨j,j.injective,fun r => hAprop (j r) (hj ⟨r,rfl⟩)⟩
  right
  have hA2 : A.card=2 := by omega
  have hC6 : C.card=6 := by omega
  obtain ⟨u,v,huv,hAuv⟩ := Finset.card_eq_two.mp hA2
  have hu := hAprop u (by rw [hAuv]; simp)
  have hv := hAprop v (by rw [hAuv]; simp)
  refine ⟨u,v,hu.1,hv.1,huv,hu.2,hv.2,?_⟩
  intro t hta htu htv
  have htC : t∈C := by
    by_contra hn
    have htA : t∈A := by simp [A,hta,hn]
    rw [hAuv] at htA
    simpa [htu,htv] using htA
  obtain ⟨s,hs,hts⟩ := Finset.mem_biUnion.mp htC
  obtain ⟨j,hjt,hsj⟩ := two_element_set_with_member s t (hedge s hs) hts
  have hjs : j∈s := by rw [hsj]; simp
  have hja : j≠a := havoid s hs j hjs
  have hju : j≠u := fun he => hu.2 s hs (he ▸ hjs)
  have hjv : j≠v := fun he => hv.2 s hs (he ▸ hjs)
  refine ⟨j,hja,hju,hjv,hjt,?_⟩
  intro k hk
  have hes : ({t,k} : Finset Coord)=s := by
    by_contra hn
    have hc := pair_family_overlap_bound F hcard hedge {t,k} s hk hs hn t (by simp) hts
    change C.card≤5 at hc
    omega
  have hj : j∈({t,k} : Finset Coord) := hes.symm ▸ hjs
  have hjk : j=k := by simpa [hjt] using hj
  exact hjk.symm

#print axioms pair_family_overlap_bound
#print axioms small_pair_family_cases
end
end Snake9
