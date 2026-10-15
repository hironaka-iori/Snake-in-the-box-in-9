import DisjointOrdinaryPartners
import StarOuterCounting

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 2200000

theorem nonordinary_pair_disjoint_one (R A B t : Finset Coord) (hAB : Disjoint A B)
    (hAR : A⊆R) (hBR : B⊆R) (ht : t.card=2) (htR : ¬t⊆R) :
    Disjoint t A ∨ Disjoint t B := by
  by_cases ha : Disjoint t A
  · exact Or.inl ha
  right
  by_contra hb
  obtain ⟨x,hxt,hxA⟩ := Finset.not_disjoint_iff.mp ha
  obtain ⟨y,hyt,hyB⟩ := Finset.not_disjoint_iff.mp hb
  have hxy : x≠y := by intro he; exact Finset.disjoint_left.mp hAB hxA (he.symm ▸ hyB)
  have hsub : ({x,y}:Finset Coord)⊆t := by simp [Finset.insert_subset_iff,hxt,hyt]
  have he : ({x,y}:Finset Coord)=t := Finset.eq_of_subset_of_card_le hsub (by simp [ht,hxy])
  apply htR
  rw [←he]
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hAR hxA
  · exact Finset.mem_singleton.mp hz ▸ hBR hyB

theorem one_ordinary_hole_good (F : Finset (Finset Coord)) (R H J s t : Finset Coord)
    (c d : Coord) (hF : F={s,t}) (hsR : s⊆R) (htR : ¬t⊆R)
    (hH : H.card=2) (hHR : H⊆R) (hHJ : Disjoint H J) (hHt : Disjoint H t)
    (hsH : s≠H) (hc : c∉R) (hd : d∉R) : OrdinaryHoleGood F R c d H J := by
  have hHF : H∉F := by
    intro hm
    rw [hF] at hm
    rcases Finset.mem_insert.mp hm with he | he
    · exact hsH he.symm
    · exact htR (Finset.mem_singleton.mp he ▸ hHR)
  refine ⟨hHF,?_,?_⟩
  · intro x hx
    have absent (z : Coord) (hz : z∉R) : ({z,x}:Finset Coord)∉F := by
      intro hm
      rw [hF] at hm
      rcases Finset.mem_insert.mp hm with he | he
      · exact hz (hsR (he ▸ (by simp : z∈({z,x}:Finset Coord))))
      · exact Finset.disjoint_left.mp hHt hx ((Finset.mem_singleton.mp he) ▸ (by simp : x∈({z,x}:Finset Coord)))
    exact ⟨absent c hc,absent d hd⟩
  · intro r hr hrH hall
    obtain ⟨x,y,hxy,hHxy⟩ := Finset.card_eq_two.mp hH
    have hxH : x∈H := by rw [hHxy]; simp
    have hyH : y∈H := by rw [hHxy]; simp
    have only_s (z : Coord) (hz : z∈H) : ({z,r}:Finset Coord)=s := by
      rcases hall z hz with hm | he
      · rw [hF] at hm
        rcases Finset.mem_insert.mp hm with he | he
        · exact he
        · apply False.elim (htR _)
          rw [←Finset.mem_singleton.mp he]
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hHR hz
          · exact Finset.mem_singleton.mp hw ▸ hr
      · exact False.elim (Finset.disjoint_left.mp hHJ hz (he ▸ (by simp : z∈({z,r}:Finset Coord))))
    have he : ({x,r}:Finset Coord)={y,r} := (only_s x hxH).trans (only_s y hyH).symm
    have hm : x∈({y,r}:Finset Coord) := he ▸ (by simp : x∈({x,r}:Finset Coord))
    rcases Finset.mem_insert.mp hm with he | he
    · exact hxy he
    · exact hrH (Finset.mem_singleton.mp he ▸ hxH)

theorem disjoint_one_ordinary_demand (F : Finset (Finset Coord)) (R A B s t : Finset Coord)
    (c d : Coord) (hR : R.card=5) (hF : F={s,t}) (hs : s.card=2) (ht : t.card=2)
    (hsR : s⊆R) (htR : ¬t⊆R) (hA : A.card=2) (hB : B.card=2)
    (hAR : A⊆R) (hBR : B⊆R) (hAB : Disjoint A B) (hc : c∉R) (hd : d∉R) :
    3≤(starIsolatedIndices R F).card+
      (F.filter (fun u => u⊆R ∧ Disjoint u A)).card+
      (F.filter (fun u => u⊆R ∧ Disjoint u B)).card+
      (if OrdinaryHoleGood F R c d A B then 1 else 0)+
      (if OrdinaryHoleGood F R c d B A then 1 else 0) := by
  have ht1 := two_edge_inter_card t R R ht (Finset.Subset.refl _) htR
  have hs2 : (s∩R).card≤2 := (Finset.card_le_card Finset.inter_subset_left).trans_eq hs
  have hb := two_edge_union_inter_bound F R s t hF hs2 ht1
  have hi := Finset.card_sdiff_add_card_inter R (F.biUnion id)
  have hI : 2≤(starIsolatedIndices R F).card := by dsimp [starIsolatedIndices]; omega
  have hsF : s∈F := by rw [hF]; simp
  by_cases hsA : Disjoint s A
  · have hpos : 1≤(F.filter (fun u => u⊆R ∧ Disjoint u A)).card :=
      Finset.card_pos.mpr ⟨s,Finset.mem_filter.mpr ⟨hsF,hsR,hsA⟩⟩
    omega
  by_cases hsB : Disjoint s B
  · have hpos : 1≤(F.filter (fun u => u⊆R ∧ Disjoint u B)).card :=
      Finset.card_pos.mpr ⟨s,Finset.mem_filter.mpr ⟨hsF,hsR,hsB⟩⟩
    omega
  have hsneA : s≠A := by intro he; exact hsB (he.symm ▸ hAB)
  have hsneB : s≠B := by intro he; exact hsA (he.symm ▸ hAB.symm)
  rcases nonordinary_pair_disjoint_one R A B t hAB hAR hBR ht htR with htA | htB
  · have hg := one_ordinary_hole_good F R A B s t c d hF hsR htR hA hAR hAB htA.symm hsneA hc hd
    rw [if_pos hg]
    omega
  · have hg := one_ordinary_hole_good F R B A s t c d hF hsR htR hB hBR hAB.symm htB.symm hsneB hc hd
    rw [if_pos hg]
    omega

#print axioms disjoint_one_ordinary_demand
end
end Snake9
