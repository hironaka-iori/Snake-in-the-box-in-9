import OrdinaryOuterCountingDefs
import EqualOuterPairCounting

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem disjoint_matching_partner_unique (A B : Finset Coord) (hA : A.card=2) (hB : B.card=2)
    (hdis : Disjoint A B) (k r t : Coord)
    (hr : ({k,r}:Finset Coord)=A ∨ ({k,r}:Finset Coord)=B)
    (ht : ({k,t}:Finset Coord)=A ∨ ({k,t}:Finset Coord)=B) : r=t := by
  have same (E : Finset Coord) (hE : E.card=2)
      (he : ({k,r}:Finset Coord)=E) (hf : ({k,t}:Finset Coord)=E) : r=t := by
    have hrk : r≠k := by
      intro hh
      rw [←he,hh] at hE
      simp at hE
    have hh : r∈({k,t}:Finset Coord) := (he.trans hf.symm) ▸ (by simp : r∈({k,r}:Finset Coord))
    exact Finset.mem_singleton.mp ((Finset.mem_insert.mp hh).resolve_left hrk)
  rcases hr with hr | hr <;> rcases ht with ht | ht
  · exact same A hA hr ht
  · exact False.elim (Finset.disjoint_left.mp hdis (hr ▸ (by simp : k∈({k,r}:Finset Coord)))
      (ht ▸ (by simp : k∈({k,t}:Finset Coord))))
  · exact False.elim (Finset.disjoint_left.mp hdis (ht ▸ (by simp : k∈({k,t}:Finset Coord)))
      (hr ▸ (by simp : k∈({k,r}:Finset Coord))))
  · exact same B hB hr ht

theorem disjoint_bad_isolated_family (F : Finset (Finset Coord)) (R A B : Finset Coord)
    (c d k : Coord) (hF : F.card=2) (hA : A.card=2) (hB : B.card=2)
    (hdis : Disjoint A B) (hc : c∉R) (hd : d∉R) (hcd : c≠d)
    (his : PairIsolated F k) (hn : ¬OrdinaryGoodRow F R A B c d k) :
    ∃r∈R,(({k,r}:Finset Coord)=A ∨ ({k,r}:Finset Coord)=B) ∧
      (F={{c,r},{d,r}} ∨ F={{c,d},{c,r}} ∨ F={{c,d},{d,r}}) := by
  have star_ne (s r : Coord) (hr : r∈R) : ({s,r}:Finset Coord)≠{c,d} := by
    intro he
    have hh : r∈({c,d}:Finset Coord) := he ▸ (by simp : r∈({s,r}:Finset Coord))
    rcases Finset.mem_insert.mp hh with he | he
    · exact hc (he ▸ hr)
    · exact hd (Finset.mem_singleton.mp he ▸ hr)
  by_cases hmcd : ({c,d}:Finset Coord)∈F
  · have hnBoth : ¬(OrdinaryPartnerClear F R A B k c ∧ OrdinaryPartnerClear F R A B k d) :=
      fun hh => hn ⟨his,Or.inl hh⟩
    by_cases hC : OrdinaryPartnerClear F R A B k c
    · have hD : ¬OrdinaryPartnerClear F R A B k d := fun hD => hnBoth ⟨hC,hD⟩
      simp only [OrdinaryPartnerClear,not_forall,Classical.not_imp,not_not] at hD
      obtain ⟨r,hr,he,hm⟩ := hD
      exact ⟨r,hr,he,Or.inr (Or.inr (pair_family_eq_two_of_mem F {c,d} {d,r}
        hF hmcd hm (Ne.symm (star_ne d r hr))))⟩
    · simp only [OrdinaryPartnerClear,not_forall,Classical.not_imp,not_not] at hC
      obtain ⟨r,hr,he,hm⟩ := hC
      exact ⟨r,hr,he,Or.inr (Or.inl (pair_family_eq_two_of_mem F {c,d} {c,r}
        hF hmcd hm (Ne.symm (star_ne c r hr))))⟩
  · have hC : ¬OrdinaryPartnerClear F R A B k c := fun hh => hn ⟨his,Or.inr ⟨hmcd,Or.inl hh⟩⟩
    have hD : ¬OrdinaryPartnerClear F R A B k d := fun hh => hn ⟨his,Or.inr ⟨hmcd,Or.inr hh⟩⟩
    simp only [OrdinaryPartnerClear,not_forall,Classical.not_imp,not_not] at hC hD
    obtain ⟨r,hr,he,hm⟩ := hC
    obtain ⟨t,ht,het,hmt⟩ := hD
    have hrt := disjoint_matching_partner_unique A B hA hB hdis k r t he het
    subst t
    have hne : ({c,r}:Finset Coord)≠{d,r} := by
      intro he
      have hh : c∈({d,r}:Finset Coord) := he ▸ (by simp : c∈({c,r}:Finset Coord))
      rcases Finset.mem_insert.mp hh with hh | hh
      · exact hcd hh
      · exact hc (Finset.mem_singleton.mp hh ▸ hr)
    exact ⟨r,hr,he,Or.inl (pair_family_eq_two_of_mem F {c,r} {d,r} hF hm hmt hne)⟩

theorem disjoint_good_rows_or_three (F : Finset (Finset Coord)) (R A B : Finset Coord)
    (c d : Coord) (hR : R.card=5) (hF : F.card=2) (hA : A.card=2) (hB : B.card=2)
    (hdis : Disjoint A B) (hc : c∉R) (hd : d∉R) (hcd : c≠d) :
    (∀k∈R,PairIsolated F k → OrdinaryGoodRow F R A B c d k) ∨
      3≤(ordinaryGoodIndices F R A B c d).card := by
  by_cases hall : ∀k∈R,PairIsolated F k → OrdinaryGoodRow F R A B c d k
  · exact Or.inl hall
  right
  push_neg at hall
  obtain ⟨k,hk,his,hn⟩ := hall
  obtain ⟨r,hr,hpartner,hfamilies⟩ := disjoint_bad_isolated_family F R A B c d k
    hF hA hB hdis hc hd hcd his hn
  have support : ∀s∈F,s⊆({c,d,r}:Finset Coord) := by
    rcases hfamilies with hfamilies | hfamilies | hfamilies <;>
      intro s hs x hx <;> rw [hfamilies] at hs <;>
      simp only [Finset.mem_insert,Finset.mem_singleton] at hs <;>
      rcases hs with rfl | rfl <;> simp_all <;> tauto
  have coord (s : Finset Coord) (hs : s∈F) (x : Coord) (hx : x∈s) (hxR : x∈R) : x=r := by
    have hh := support s hs hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with he | he | he
    · exact False.elim (hc (he ▸ hxR))
    · exact False.elim (hd (he ▸ hxR))
    · exact he
  let D := R\{r,k}
  have hD : 3≤D.card := by
    have hcount := Finset.card_sdiff_add_card_inter R ({r,k}:Finset Coord)
    have hi : (R∩({r,k}:Finset Coord)).card≤2 :=
      (Finset.card_le_card Finset.inter_subset_right).trans Finset.card_le_two
    dsimp [D]
    omega
  have hsub : D⊆ordinaryGoodIndices F R A B c d := by
    intro v hv
    obtain ⟨hvR,hvN⟩ := Finset.mem_sdiff.mp hv
    have hvr : v≠r := by intro he; exact hvN (by simp [he])
    have hvk : v≠k := by intro he; exact hvN (by simp [he])
    have hisv : PairIsolated F v := fun s hs hvs => hvr (coord s hs v hvs hvR)
    have clear (z : Coord) : OrdinaryPartnerClear F R A B v z := by
      intro t ht hvt hzt
      have htr : t=r := coord _ hzt t (by simp) ht
      have hrv : ({r,v}:Finset Coord)=A ∨ ({r,v}:Finset Coord)=B := by
        simpa only [htr,Finset.pair_comm v r] using hvt
      have hrk : ({r,k}:Finset Coord)=A ∨ ({r,k}:Finset Coord)=B := by
        simpa only [Finset.pair_comm k r] using hpartner
      exact hvk (disjoint_matching_partner_unique A B hA hB hdis r v k hrv hrk)
    exact Finset.mem_filter.mpr ⟨hvR,hisv,Or.inl ⟨clear c,clear d⟩⟩
  exact hD.trans (Finset.card_le_card hsub)

#print axioms disjoint_bad_isolated_family
#print axioms disjoint_good_rows_or_three
end
end Snake9
