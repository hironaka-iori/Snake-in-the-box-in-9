import SmallPairFamilies

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

theorem pair_family_other_edge (F : Finset (Finset Coord)) (s : Finset Coord)
    (hF : F.card=2) (hs : s∈F) : ∃t : Finset Coord,t≠s ∧ t∈F ∧ F={s,t} := by
  have hc : (F.erase s).card=1 := by rw [Finset.card_erase_of_mem hs,hF]
  obtain ⟨t,ht⟩ := Finset.card_eq_one.mp hc
  have htm : t∈F.erase s := by rw [ht]; simp
  obtain ⟨hts,htF⟩ := Finset.mem_erase.mp htm
  refine ⟨t,hts,htF,?_⟩
  have he := Finset.insert_erase hs
  rw [ht] at he
  exact he.symm

theorem two_edge_inter_card (s A R : Finset Coord) (hs : s.card=2)
    (hAR : A⊆R) (hn : ¬s⊆R) : (s∩A).card≤1 := by
  by_contra hh
  have hsub : s∩A⊆s := Finset.inter_subset_left
  have he : s∩A=s := Finset.eq_of_subset_of_card_le hsub (by omega)
  apply hn
  rw [←he]
  exact Finset.Subset.trans Finset.inter_subset_right hAR

theorem family_isolated_embedding (F : Finset (Finset Coord)) (A : Finset Coord) (n : Nat)
    (hcard : n+(A∩F.biUnion id).card≤A.card) :
    ∃j : Fin n → Coord,Function.Injective j ∧ ∀r,j r∈A ∧ PairIsolated F (j r) := by
  let B := A\F.biUnion id
  have hc := Finset.card_sdiff_add_card_inter A (F.biUnion id)
  have hb : n≤B.card := by dsimp [B]; omega
  obtain ⟨j,hj⟩ := Function.Embedding.exists_of_card_le_finset (show Fintype.card (Fin n)≤B.card by simpa using hb)
  refine ⟨j,j.injective,?_⟩
  intro r
  obtain ⟨hrA,hrF⟩ := Finset.mem_sdiff.mp (hj ⟨r,rfl⟩)
  refine ⟨hrA,?_⟩
  intro s hs hrs
  exact hrF (Finset.mem_biUnion.mpr ⟨s,hs,hrs⟩)

theorem two_edge_union_inter_bound (F : Finset (Finset Coord)) (A s t : Finset Coord)
    (hF : F={s,t}) (hs : (s∩A).card≤2) (ht : (t∩A).card≤1) :
    (A∩F.biUnion id).card≤3 := by
  have he : A∩F.biUnion id=(s∩A)∪(t∩A) := by
    ext x
    simp [hF]
    tauto
  rw [he]
  have hu := Finset.card_union_le (s∩A) (t∩A)
  omega

theorem common_hole_rr_cases (R : Finset Coord) (e : Coord) (F : Finset (Finset Coord))
    (hR : R.card=5) (he : e∈R) (hF : F.card=2) (hedge : ∀s∈F,s.card=2)
    (s : Finset Coord) (hs : s∈F) (hsR : s⊆R) :
    (∃t∈F,t≠s ∧ t⊆R) ∨ ∃k : Coord,k∈R ∧ k≠e ∧ PairIsolated F k := by
  obtain ⟨t,hts,htF,hst⟩ := pair_family_other_edge F s hF hs
  by_cases htR : t⊆R
  · exact Or.inl ⟨t,htF,hts,htR⟩
  right
  let A := R.erase e
  have hA : A.card=4 := by dsimp [A]; rw [Finset.card_erase_of_mem he,hR]
  have hAs : (s∩A).card≤2 := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans (by rw [hedge s hs])
  have hAt : (t∩A).card≤1 := two_edge_inter_card t A R (hedge t htF) (Finset.erase_subset _ _) htR
  have hbound := two_edge_union_inter_bound F A s t hst hAs hAt
  obtain ⟨j,_,hj⟩ := family_isolated_embedding F A 1 (by omega)
  obtain ⟨hk,hiso⟩ := hj 0
  obtain ⟨hke,hkR⟩ := Finset.mem_erase.mp hk
  exact ⟨j 0,hkR,hke,hiso⟩

theorem common_hole_cd_three_isolated (R : Finset Coord) (e c d : Coord)
    (F : Finset (Finset Coord)) (hR : R.card=5) (he : e∈R)
    (hc : c∉R) (hd : d∉R) (hF : F.card=2) (hedge : ∀s∈F,s.card=2)
    (hnRR : ∀s∈F,¬s⊆R) (hcd : ({c,d}:Finset Coord)∈F) :
    ∃j : Fin 3 → Coord,Function.Injective j ∧
      ∀r,j r∈R ∧ j r≠e ∧ PairIsolated F (j r) := by
  obtain ⟨t,_,htF,hst⟩ := pair_family_other_edge F {c,d} hF hcd
  let A := R.erase e
  have hA : A.card=4 := by dsimp [A]; rw [Finset.card_erase_of_mem he,hR]
  have hcA : c∉A := fun hh => hc (Finset.mem_erase.mp hh).2
  have hdA : d∉A := fun hh => hd (Finset.mem_erase.mp hh).2
  have hAt : (t∩A).card≤1 := two_edge_inter_card t A R (hedge t htF) (Finset.erase_subset _ _) (hnRR t htF)
  have heq : A∩F.biUnion id=t∩A := by
    ext x
    simp only [hst,Finset.mem_inter,Finset.mem_biUnion,Finset.mem_insert,Finset.mem_singleton, id_eq]
    constructor
    · rintro ⟨hx,⟨s,hs,hxs⟩⟩
      rcases hs with rfl | rfl
      · rcases Finset.mem_insert.mp hxs with hec | hed
        · exact False.elim (hcA (hec ▸ hx))
        · exact False.elim (hdA (Finset.mem_singleton.mp hed ▸ hx))
      · exact ⟨hxs,hx⟩
    · rintro ⟨hxt,hx⟩
      exact ⟨hx,t,Or.inr rfl,hxt⟩
  have hbound : (A∩F.biUnion id).card≤1 := by rw [heq]; exact hAt
  obtain ⟨j,hj,his⟩ := family_isolated_embedding F A 3 (by omega)
  refine ⟨j,hj,?_⟩
  intro r
  obtain ⟨hr,hiso⟩ := his r
  obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hr
  exact ⟨hm,hne,hiso⟩

theorem common_hole_double_star_three_isolated (R : Finset Coord) (e c d i : Coord)
    (F : Finset (Finset Coord)) (hR : R.card=5) (he : e∈R)
    (hc : c∉R) (hd : d∉R) (hcd : c≠d) (hi : i∈R)
    (hF : F.card=2) (hci : ({c,i}:Finset Coord)∈F) (hdi : ({d,i}:Finset Coord)∈F) :
    ∃j : Fin 3 → Coord,Function.Injective j ∧
      ∀r,j r∈R ∧ j r≠e ∧ PairIsolated F (j r) := by
  have hci_ne_di : ({c,i}:Finset Coord)≠{d,i} := by
    intro heq
    have hm : c∈({d,i}:Finset Coord) := heq ▸ (by simp)
    rcases Finset.mem_insert.mp hm with heq | heq
    · exact hcd heq
    · exact hc (Finset.mem_singleton.mp heq ▸ hi)
  have hFeq : F={{c,i},{d,i}} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hci
      · exact Finset.mem_singleton.mp hs ▸ hdi
    · simp [hF,hci_ne_di]
  let A := R.erase e
  have hA : A.card=4 := by dsimp [A]; rw [Finset.card_erase_of_mem he,hR]
  have hcA : c∉A := fun hh => hc (Finset.mem_erase.mp hh).2
  have hdA : d∉A := fun hh => hd (Finset.mem_erase.mp hh).2
  have hsub : A∩F.biUnion id⊆{i} := by
    intro x hx
    obtain ⟨hxA,hxF⟩ := Finset.mem_inter.mp hx
    obtain ⟨s,hs,hxs⟩ := Finset.mem_biUnion.mp hxF
    rw [hFeq] at hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · rcases Finset.mem_insert.mp hxs with rfl | hh
      · exact False.elim (hcA hxA)
      · exact hh
    · have heq := Finset.mem_singleton.mp hs
      rw [heq] at hxs
      rcases Finset.mem_insert.mp hxs with rfl | hh
      · exact False.elim (hdA hxA)
      · exact hh
  have hbound : (A∩F.biUnion id).card≤1 := (Finset.card_le_card hsub).trans (by simp)
  obtain ⟨j,hj,his⟩ := family_isolated_embedding F A 3 (by omega)
  refine ⟨j,hj,?_⟩
  intro r
  obtain ⟨hr,hiso⟩ := his r
  obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hr
  exact ⟨hm,hne,hiso⟩

#print axioms common_hole_rr_cases
#print axioms common_hole_cd_three_isolated
#print axioms common_hole_double_star_three_isolated
end
end Snake9
