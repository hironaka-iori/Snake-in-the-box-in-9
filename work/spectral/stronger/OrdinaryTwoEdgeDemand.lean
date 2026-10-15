import OrdinaryOuterCountingDefs
import StarOuterCounting

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 2200000

theorem ordinary_bad_hole_replacement (R E G : Finset Coord) (F : Finset (Finset Coord))
    (c d : Coord) (hR : R.card=5) (hE : E.card=2) (hG : G.card=2)
    (hF : F.card=2) (hsub : ∀s∈F,s⊆R) (hdis : Disjoint E G)
    (hc : c∉R) (hd : d∉R) (hen : E∉F)
    (hbad : ¬OrdinaryHoleGood F R c d E G) :
    2≤(starIsolatedIndices R F).card ∧ OrdinaryHoleGood F R c d G E := by
  have hstars (s : Coord) : ({c,s}:Finset Coord)∉F ∧ ({d,s}:Finset Coord)∉F := by
    exact ⟨fun hh => hc (hsub _ hh (by simp)),fun hh => hd (hsub _ hh (by simp))⟩
  have hw : ¬∀r∈R,r∉E → ¬∀s∈E,({s,r}:Finset Coord)∈F ∨ ({s,r}:Finset Coord)=G := by
    intro hh
    exact hbad ⟨hen,fun s _ => hstars s,hh⟩
  push_neg at hw
  obtain ⟨r,hr,hrE,hpairs⟩ := hw
  have hpairs' (s : Coord) (hs : s∈E) : ({s,r}:Finset Coord)∈F := by
    rcases hpairs s hs with hh | hh
    · exact hh
    · exact False.elim (Finset.disjoint_left.mp hdis hs (hh ▸ (by simp : s∈({s,r}:Finset Coord))))
  obtain ⟨i,j,hij,hEeq⟩ := Finset.card_eq_two.mp hE
  have hi : i∈E := by rw [hEeq]; simp
  have hj : j∈E := by rw [hEeq]; simp
  have hri : r≠i := fun hh => hrE (hh.symm ▸ hi)
  have hrj : r≠j := fun hh => hrE (hh.symm ▸ hj)
  have hne : ({i,r}:Finset Coord)≠{j,r} := by
    intro hh
    have hm : i∈({j,r}:Finset Coord) := hh ▸ (by simp)
    simpa [hij,Ne.symm hri] using hm
  have hFs : ({{i,r},{j,r}}:Finset (Finset Coord))⊆F := by
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hpairs' i hi
    · exact Finset.mem_singleton.mp hs ▸ hpairs' j hj
  have hFeq : F={{i,r},{j,r}} :=
    (Finset.eq_of_subset_of_card_le hFs (by simp [hF,hne])).symm
  have hU : F.biUnion id=insert r E := by
    ext k
    simp [hFeq,hEeq]
    tauto
  have hsmall : (R∩F.biUnion id).card≤3 := by
    have hh := Finset.card_le_card (Finset.inter_subset_right : R∩F.biUnion id⊆F.biUnion id)
    rw [hU,Finset.card_insert_of_not_mem hrE,hE] at hh
    simpa only [←hU] using hh
  have hI : 2≤(starIsolatedIndices R F).card := by
    have hh := Finset.card_sdiff_add_card_inter R (F.biUnion id)
    dsimp [starIsolatedIndices]
    omega
  have hgn : G∉F := by
    intro hg
    rw [hFeq] at hg
    rcases Finset.mem_insert.mp hg with he | he
    · exact Finset.disjoint_left.mp hdis hi (he.symm ▸ (by simp : i∈({i,r}:Finset Coord)))
    · exact Finset.disjoint_left.mp hdis hj ((Finset.mem_singleton.mp he).symm ▸ (by simp : j∈({j,r}:Finset Coord)))
  obtain ⟨u,v,huv,hGeq⟩ := Finset.card_eq_two.mp hG
  have hfresh : ∃l∈G,l≠r := by
    by_cases hur : u=r
    · exact ⟨v,by rw [hGeq]; simp,fun he => huv (hur.trans he.symm)⟩
    · exact ⟨u,by rw [hGeq]; simp,hur⟩
  obtain ⟨l,hlG,hlr⟩ := hfresh
  have hlE : l∉E := fun hh => Finset.disjoint_left.mp hdis hh hlG
  have hlU : l∉F.biUnion id := by simpa only [hU,Finset.mem_insert,not_or] using And.intro hlr hlE
  refine ⟨hI,hgn,fun s _ => hstars s,?_⟩
  intro k hk hkG hp
  rcases hp l hlG with hh | hh
  · exact hlU (Finset.mem_biUnion.mpr ⟨{l,k},hh,by simp⟩)
  · exact hlE (hh ▸ (by simp : l∈({l,k}:Finset Coord)))

theorem ordinary_two_edge_demand (R A B : Finset Coord) (F : Finset (Finset Coord))
    (c d : Coord) (hR : R.card=5) (hA : A.card=2) (hB : B.card=2)
    (hF : F.card=2) (hpair : ∀s∈F,s.card=2) (hsub : ∀s∈F,s⊆R)
    (hdis : Disjoint A B) (hc : c∉R) (hd : d∉R) :
    3≤(starIsolatedIndices R F).card+
      (F.filter (fun s => Disjoint s A)).card+(F.filter (fun s => Disjoint s B)).card+
      (if OrdinaryHoleGood F R c d A B then 1 else 0)+
      (if OrdinaryHoleGood F R c d B A then 1 else 0) := by
  have hI : 1≤(starIsolatedIndices R F).card := by
    have hc' := Finset.card_sdiff_add_card_inter R (F.biUnion id)
    have hu := pair_family_union_card F hpair
    have hb := Finset.card_le_card (Finset.inter_subset_right : R∩F.biUnion id⊆F.biUnion id)
    dsimp [starIsolatedIndices]
    omega
  have haCharge (ha : A∈F) : 1≤(F.filter (fun s => Disjoint s B)).card :=
    Finset.one_le_card.mpr ⟨A,Finset.mem_filter.mpr ⟨ha,hdis⟩⟩
  have hbCharge (hb : B∈F) : 1≤(F.filter (fun s => Disjoint s A)).card :=
    Finset.one_le_card.mpr ⟨B,Finset.mem_filter.mpr ⟨hb,hdis.symm⟩⟩
  by_cases hga : OrdinaryHoleGood F R c d A B
  · rw [if_pos hga]
    by_cases hgb : OrdinaryHoleGood F R c d B A
    · rw [if_pos hgb]; omega
    · rw [if_neg hgb]
      by_cases hb : B∈F
      · have hh := hbCharge hb; omega
      · have hh := ordinary_bad_hole_replacement R B A F c d hR hB hA hF hsub hdis.symm hc hd hb hgb
        omega
  · rw [if_neg hga]
    by_cases ha : A∈F
    · have hh := haCharge ha
      by_cases hgb : OrdinaryHoleGood F R c d B A
      · rw [if_pos hgb]; omega
      · rw [if_neg hgb]
        by_cases hb : B∈F
        · have hh' := hbCharge hb; omega
        · exact False.elim (hga (ordinary_bad_hole_replacement R B A F c d hR hB hA hF hsub hdis.symm hc hd hb hgb).2)
    · have hh := ordinary_bad_hole_replacement R A B F c d hR hA hB hF hsub hdis hc hd ha hga
      rw [if_pos hh.2]
      omega

#print axioms ordinary_two_edge_demand
end
end Snake9
