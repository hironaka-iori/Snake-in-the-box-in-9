import CommonHoleCounting
import PairFamilySplitting

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 2000000

def starIsolatedIndices (R : Finset Coord) (F : Finset (Finset Coord)) : Finset Coord :=
  R\F.biUnion id

def starOrdinaryEdges (R : Finset Coord) (F : Finset (Finset Coord)) : Finset (Finset Coord) :=
  F.filter (fun s => s⊆R)

def starEndpointCount (R : Finset Coord) (F : Finset (Finset Coord)) (e f : Coord) : Nat :=
  (starIsolatedIndices R F).card + ((starOrdinaryEdges R F).filter (fun s => e∉s)).card +
    ((starOrdinaryEdges R F).filter (fun s => f∉s)).card

theorem family_two_edge_inter_bound (F : Finset (Finset Coord)) (s t R : Finset Coord)
    (hF : F={s,t}) : (R∩F.biUnion id).card≤(s∩R).card+(t∩R).card := by
  have he : R∩F.biUnion id=(s∩R)∪(t∩R) := by
    ext x
    simp [hF]
    tauto
  rw [he]
  exact Finset.card_union_le _ _

/-- A symbolic two-edge argument. No enumeration of coordinates or families is used. -/
theorem star_outer_small_endpoint_count (R : Finset Coord) (c e f : Coord)
    (F : Finset (Finset Coord)) (hR : R.card=5) (hcR : c∉R)
    (hF : F.card=2) (hedge : ∀s∈F,s.card=2)
    (hcount : starEndpointCount R F e f≤2) :
    (starIsolatedIndices R F).card=2 ∧
      ∃y : Coord,y∈R ∧ y≠f ∧ ({f,y}:Finset Coord)∈F ∧ ({c,y}:Finset Coord)∉F := by
  let I := starIsolatedIndices R F
  let RR := starOrdinaryEdges R F
  have hc : I.card+(R∩F.biUnion id).card=5 := by
    exact (Finset.card_sdiff_add_card_inter R (F.biUnion id)).trans (by rw [hR])
  have hbound : (R∩F.biUnion id).card≤4 := by
    have hi := Finset.card_le_card (Finset.inter_subset_right : R∩F.biUnion id⊆F.biUnion id)
    have hu := pair_family_union_card F hedge
    omega
  have hI1 : 1≤I.card := by omega
  change I.card+(RR.filter (fun s => e∉s)).card+(RR.filter (fun s => f∉s)).card≤2 at hcount
  have existsRR : ∃s∈F,s⊆R := by
    by_contra hn
    have hnR : ∀s∈F,¬s⊆R := by intro s hs hr; exact hn ⟨s,hs,hr⟩
    obtain ⟨s,t,hst,hFst⟩ := Finset.card_eq_two.mp hF
    have hsF : s∈F := by rw [hFst]; simp
    have htF : t∈F := by rw [hFst]; simp
    have hsi := two_edge_inter_card s R R (hedge s hsF) (Finset.Subset.refl _) (hnR s hsF)
    have hti := two_edge_inter_card t R R (hedge t htF) (Finset.Subset.refl _) (hnR t htF)
    have hcover := family_two_edge_inter_bound F s t R hFst
    omega
  obtain ⟨s,hsF,hsR⟩ := existsRR
  obtain ⟨t,hts,htF,hFst⟩ := pair_family_other_edge F s hF hsF
  have hI2 : 2≤I.card := by
    by_cases htR : t⊆R
    · by_contra hn
      have hIeq : I.card=1 := by omega
      have hUR : F.biUnion id⊆R := by
        intro k hk
        obtain ⟨q,hq,hkq⟩ := Finset.mem_biUnion.mp hk
        rw [hFst] at hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hsR hkq
        · exact htR (Finset.mem_singleton.mp hq ▸ hkq)
      have hU4 : (F.biUnion id).card=4 := by
        have he : R∩F.biUnion id=F.biUnion id := Finset.inter_eq_right.mpr hUR
        rw [he] at hc
        omega
      have hdis := pair_family_disjoint_of_card_union F hF hedge hU4 s t hsF htF (Ne.symm hts)
      have positive (x : Coord) : 1≤(RR.filter (fun q => x∉q)).card := by
        apply Finset.one_le_card.mpr
        by_cases hx : x∈s
        · have hxt : x∉t := fun hh => Finset.disjoint_left.mp hdis hx hh
          exact ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨htF,htR⟩,hxt⟩⟩
        · exact ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hsF,hsR⟩,hx⟩⟩
      have he := positive e
      have hf := positive f
      omega
    · have hti := two_edge_inter_card t R R (hedge t htF) (Finset.Subset.refl _) htR
      have hsi : (s∩R).card≤2 := (Finset.card_le_card Finset.inter_subset_left).trans (by rw [hedge s hsF])
      have hcover := family_two_edge_inter_bound F s t R hFst
      omega
  have hIeq : I.card=2 := by omega
  have hright0 : (RR.filter (fun q => f∉q)).card=0 := by omega
  have hfs : f∈s := by
    by_contra hn
    have hm : s∈RR.filter (fun q => f∉q) := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hsF,hsR⟩,hn⟩
    rw [Finset.card_eq_zero.mp hright0] at hm
    exact Finset.not_mem_empty _ hm
  obtain ⟨y,hyf,hsfy⟩ := two_element_set_with_member s f (hedge s hsF) hfs
  have hys : y∈s := by rw [hsfy]; simp
  have hyR := hsR hys
  have hfy : ({f,y}:Finset Coord)∈F := hsfy ▸ hsF
  have hcy : ({c,y}:Finset Coord)∉F := by
    intro hcy
    rw [hFst] at hcy
    rcases Finset.mem_insert.mp hcy with hcys | hcyt
    · have hcs : c∈s := hcys ▸ (by simp)
      exact hcR (hsR hcs)
    · have htcy : t=({c,y}:Finset Coord) := (Finset.mem_singleton.mp hcyt).symm
      have hsub : R∩F.biUnion id⊆s := by
        intro k hk
        obtain ⟨hkR,hkU⟩ := Finset.mem_inter.mp hk
        have hU : F.biUnion id=s∪t := by simp [hFst]
        rw [hU,htcy] at hkU
        rcases Finset.mem_union.mp hkU with hks | hkt
        · exact hks
        · rcases Finset.mem_insert.mp hkt with hkc | hky
          · exact False.elim (hcR (hkc ▸ hkR))
          · exact (Finset.mem_singleton.mp hky).symm ▸ hys
      have hsmall : (R∩F.biUnion id).card≤2 := (Finset.card_le_card hsub).trans (by rw [hedge s hsF])
      omega
  exact ⟨hIeq,y,hyR,hyf,hfy,hcy⟩

#print axioms star_outer_small_endpoint_count
end
end Snake9
