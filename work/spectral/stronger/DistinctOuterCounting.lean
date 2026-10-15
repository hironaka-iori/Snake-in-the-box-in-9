import DistinctOuterConfig

namespace Snake9
open scoped BigOperators
open Finset Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem outer_zero_delta_count_false (R H : Finset Coord) (G J : Finset (Finset Coord))
    (c d : Coord) (hR : R.card=5) (hH : H⊆R)
    (hGc : G.card+H.card=2) (hJc : J.card+H.card=2)
    (hG : ∀s∈G,s.card=2) (hJ : ∀s∈J,s.card=2)
    (hcover : R\H⊆outerEdgeResources (H∪{c,d}) G J) : False := by
  have hc := Finset.card_le_card hcover
  have hb := outerEdgeResources_card (H∪{c,d}) G J hG hJ
  have hRH : (R\H).card=5-H.card := by rw [Finset.card_sdiff hH,hR]
  omega

theorem outer_one_delta_count (R H E : Finset Coord) (G J : Finset (Finset Coord))
    (c : Coord) (hR : R.card=5) (hH : H⊆R) (hEc : E.card≤2)
    (hGc : G.card+H.card=1) (hJc : J.card+H.card=2)
    (hG : ∀s∈G,s.card=2) (hJ : ∀s∈J,s.card=2)
    (hcover : R\H⊆E∪outerEdgeResources (H∪{c}) G J) :
    H=∅ ∧ G.card=1 ∧ J.card=2 ∧ (outerEdgeResources {c} G J).card=3 := by
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le E (outerEdgeResources (H∪{c}) G J)
  have hb := outerEdgeResources_card (H∪{c}) G J hG hJ
  have hRH : (R\H).card=5-H.card := by rw [Finset.card_sdiff hH,hR]
  have hHc : H.card=0 := by omega
  have hz : H=∅ := Finset.card_eq_zero.mp hHc
  have he : H∪{c}=({c}:Finset Coord) := by simp [hz]
  rw [he] at hc hu hb
  exact ⟨hz,by omega,by omega,by omega⟩

theorem one_delta_resource_shape (R : Finset Coord) (G J : Finset (Finset Coord))
    (c d : Coord) (hcd : c≠d) (hcR : c∉R) (hdR : d∉R)
    (hGc : G.card=1) (hJc : J.card=2)
    (hG : ∀s∈G,s.card=2) (hJ : ∀s∈J,s.card=2)
    (hGr : ∀s∈G,s⊆insert d R) (hJr : ∀s∈J,s⊆insert c R)
    (hC : (outerEdgeResources {c} G J).card=3) :
    ∃i j k : Coord,i∈R ∧ j∈R ∧ k∈R ∧ i≠j ∧ i≠k ∧ j≠k ∧
      G={{i,j}} ∧ J={{i,j},{c,k}} := by
  obtain ⟨s,hGs⟩ := Finset.card_eq_one.mp hGc
  have hsG : s∈G := by rw [hGs]; simp
  have hs2 := hG s hsG
  have hcs : c∉s := by
    intro hh
    have hr := hGr s hsG hh
    simpa [hcd,hcR] using hr
  have hzeroG : ∀t∈G,holeEdgeResource {c} t=∅ := by
    intro t ht
    have he : t=s := by simpa [hGs] using ht
    subst t
    have hn : ¬(s∩({c}:Finset Coord)).Nonempty := by
      rintro ⟨x,hx⟩
      obtain ⟨hxs,hxc⟩ := Finset.mem_inter.mp hx
      exact hcs (Finset.mem_singleton.mp hxc ▸ hxs)
    simp only [holeEdgeResource,if_neg hn]
  have noJ (hn : s∉J) : False := by
    have hres : outerEdgeResources {c} G J=J.biUnion (holeEdgeResource {c}) := by
      ext k
      simp only [outerEdgeResources,Finset.mem_union,Finset.mem_biUnion,Finset.mem_inter,
        Finset.mem_sdiff]
      constructor
      · rintro ((⟨t,⟨htG,htJ⟩,hkt⟩ | ⟨t,⟨htG,_⟩,hkt⟩) | ⟨t,⟨htJ,_⟩,hkt⟩)
        · have he : t=s := by simpa [hGs] using htG
          exact False.elim (hn (he ▸ htJ))
        · rw [hzeroG t htG] at hkt
          exact False.elim (Finset.not_mem_empty _ hkt)
        · exact ⟨t,htJ,hkt⟩
      · rintro ⟨t,htJ,hkt⟩
        right
        refine ⟨t,⟨htJ,?_⟩,hkt⟩
        intro htG
        have he : t=s := by simpa [hGs] using htG
        exact hn (he ▸ htJ)
    have hb : (J.biUnion (holeEdgeResource {c})).card≤2 := by
      calc
        _ ≤ ∑t∈J,(holeEdgeResource {c} t).card := Finset.card_biUnion_le
        _ ≤ ∑t∈J,1 := Finset.sum_le_sum (fun t ht => holeEdgeResource_card _ t (hJ t ht))
        _ = 2 := by simp [hJc]
    rw [hres] at hC
    omega
  have hsJ : s∈J := not_not.mp noJ
  have hJrem : (J\{s}).card=1 := by
    rw [Finset.card_sdiff (Finset.singleton_subset_iff.mpr hsJ),hJc]
    simp
  obtain ⟨t,hrem⟩ := Finset.card_eq_one.mp hJrem
  have htrem : t∈J\{s} := by rw [hrem]; simp
  have htJ := (Finset.mem_sdiff.mp htrem).1
  have hts : t≠s := by simpa using (Finset.mem_sdiff.mp htrem).2
  have hJst : J={s,t} := by
    apply Finset.ext
    intro q
    constructor
    · intro hq
      by_cases he : q=s
      · simp [he]
      · have hm : q∈J\{s} := Finset.mem_sdiff.mpr ⟨hq,by simpa using he⟩
        rw [hrem] at hm
        simp [Finset.mem_singleton.mp hm]
    · intro hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hsJ
      · exact Finset.mem_singleton.mp hq ▸ htJ
  have hres : outerEdgeResources {c} G J=s∪holeEdgeResource {c} t := by
    ext k
    simp [outerEdgeResources,hGs,hJst,hts,Ne.symm hts]
    aesop
  have noC (hn : c∉t) : False := by
    have hz : holeEdgeResource {c} t=∅ := by
      have hn' : ¬(t∩({c}:Finset Coord)).Nonempty := by
        rintro ⟨x,hx⟩
        obtain ⟨hxt,hxc⟩ := Finset.mem_inter.mp hx
        exact hn (Finset.mem_singleton.mp hxc ▸ hxt)
      simp [holeEdgeResource,hn']
    rw [hres,hz,Finset.union_empty,hs2] at hC
    omega
  have hct : c∈t := not_not.mp noC
  obtain ⟨k,hkc,htck⟩ := two_element_set_with_member t c (hJ t htJ) hct
  have hkR : k∈R := by
    have hkt : k∈t := by rw [htck]; simp
    have hh := hJr t htJ hkt
    simpa [hkc] using hh
  have hQ : holeEdgeResource {c} t={k} := by
    have ht : (t∩({c}:Finset Coord)).Nonempty := ⟨c,by simp [hct]⟩
    rw [holeEdgeResource,if_pos ht,htck]
    ext x
    by_cases hxk : x=k
    · simp [hxk,hkc]
    · simp [hxk]
  have hks : k∉s := by
    intro hh
    have he : s∪{k}=s := Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr hh)
    rw [hres,hQ,he,hs2] at hC
    omega
  have hsR : s⊆R := by
    intro x hx
    have hh := hJr s hsJ hx
    exact (Finset.mem_insert.mp hh).resolve_left (fun he => hcs (he ▸ hx))
  obtain ⟨i,j,hij,hsij⟩ := Finset.card_eq_two.mp hs2
  have hiR := hsR (show i∈s by rw [hsij]; simp)
  have hjR := hsR (show j∈s by rw [hsij]; simp)
  have hik : i≠k := by intro he; exact hks (he ▸ (show i∈s by rw [hsij]; simp))
  have hjk : j≠k := by intro he; exact hks (he ▸ (show j∈s by rw [hsij]; simp))
  exact ⟨i,j,k,hiR,hjR,hkR,hij,hik,hjk,by rw [hGs,hsij],by rw [hJst,hsij,htck]⟩

#print axioms outer_zero_delta_count_false
#print axioms outer_one_delta_count
#print axioms one_delta_resource_shape
end
end Snake9
