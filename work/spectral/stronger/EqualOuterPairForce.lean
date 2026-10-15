import EqualOuterPairEndpoints
import EqualOuterPairCounting
import CommonHoleEndpointGroups

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 2400000

namespace EqualOuterPairConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : EqualOuterPairConfig p a b c d)
include h

theorem clean_card : h.clean.card=3 := by
  have hR : (distinctR a b c d).card=5 := by
    simp [distinctR,Finset.card_sdiff (Finset.subset_univ _),Coord,h.outer.hab,h.outer.hac,
      h.outer.had,h.outer.hbc,h.outer.hbd,h.outer.hcd]
  have hsub : ({h.i,h.j}:Finset Coord)⊆distinctR a b c d := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h.hi
    · exact Finset.mem_singleton.mp hx ▸ h.hj
  simp [clean,Finset.card_sdiff hsub,hR,h.hij]

theorem clean_avoids : h.i∉h.clean ∧ h.j∉h.clean ∧ c∉h.clean ∧ d∉h.clean := by
  simp [clean,distinctR]

theorem clean_pair_disjoint (x y : Coord) (hx : x∉h.clean) (hy : y∉h.clean) :
    Disjoint ({x,y}:Finset Coord) h.clean := by
  apply Finset.disjoint_left.mpr
  intro z hz hzC
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact hx hzC
  · exact hy (Finset.mem_singleton.mp hz ▸ hzC)

theorem three_clean_isolated_false (f : MissingAtNeighbor p a b)
    (u : Fin 3 → Coord) (hinj : Function.Injective u)
    (hu : ∀r,u r∈h.clean ∧ PairIsolated f.F (u r)) : False := by
  apply three_active_endpoint_groups_false p a b c d u hinj
    (fun r => ((h.mem_clean _).mp (hu r).1).1)
  intro r
  obtain ⟨v,hv,hl,hg⟩ := h.isolated_endpoint f (u r) (hu r).1 (hu r).2
  refine ⟨v,hv,hl,?_⟩
  rcases hg with hh | hh | hh
  · exact Or.inl hh
  · exact Or.inr (Or.inl hh)
  · exact Or.inr (Or.inr (Or.inl hh))

theorem two_clean_isolated_hole_not_low (f : MissingAtNeighbor p a b)
    (u : Fin 2 → Coord) (hinj : Function.Injective u)
    (hu : ∀r,u r∈h.clean ∧ PairIsolated f.F (u r))
    (ht : InPath p (triple a h.i h.j)) : ¬AtMostOneNeighbor p (triple a h.i h.j) := by
  have h01 : u 0≠u 1 := fun he => (by decide : (0:Fin 2)≠1) (hinj he)
  have hb (r : Fin 2) : (triple a h.i h.j).val.testBit (u r).val=false := by
    obtain ⟨hr,hri,hrj⟩ := (h.mem_clean _).mp (hu r).1
    have hra := ((mem_distinctR a b c d _).mp hr).1
    simp [bit_triple,Ne.symm hra,Ne.symm hri,Ne.symm hrj]
  exact h.nonlow_outside_two f (u 0) (u 1) (hu 0).1 (hu 1).1 h01 (hu 0).2 (hu 1).2
    _ ht (hb 0) (hb 1)

theorem missing_clean_and_isolated_false (f : MissingAtNeighbor p a b)
    (x y k : Coord) (hx : x∈h.clean) (hy : y∈h.clean) (hxy : x≠y)
    (hm : ({x,y}:Finset Coord)∈f.F) (hk : k∈h.clean) (his : PairIsolated f.F k) : False := by
  have hxR := ((h.mem_clean x).mp hx).1
  have hyR := ((h.mem_clean y).mp hy).1
  have hkR := ((h.mem_clean k).mp hk).1
  have hs := h.clean_corners x y hx hyR hxy
  have hl := h.missing_clean_pair_low f x y hx hy hxy hm
  have hl' := h.missing_clean_quad_low f x y hx hy hxy hm
  obtain ⟨v,hv,hlv,hg⟩ := h.isolated_endpoint f k hk his
  have hkx : k≠x := by intro he; exact his _ hm (by simp [he])
  have hky : k≠y := by intro he; exact his _ hm (by simp [he])
  have hx' := (mem_distinctR a b c d x).mp hxR
  have hy' := (mem_distinctR a b c d y).mp hyR
  have hk' := (mem_distinctR a b c d k).mp hkR
  have hn : pair x y≠quad a b x y := by
    intro he
    have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    simp [bit_pair,bit_quad,Ne.symm h.outer.hab,hx'.1,hy'.1] at hb
  have hn0 : v≠pair x y := by
    intro he
    have hb := h.resource_bit_self k hkR v hg
    rw [he] at hb
    simp [bit_pair,Ne.symm hkx,Ne.symm hky] at hb
  have hn1 : v≠quad a b x y := by
    intro he
    have hb := h.resource_bit_self k hkR v hg
    rw [he] at hb
    simp [bit_quad,Ne.symm hk'.1,Ne.symm hk'.2.1,Ne.symm hkx,Ne.symm hky] at hb
  rcases three_low_degree_vertices_repeat p hs.1 hs.2 hv hl hl' hlv with he | he | he
  · exact hn he
  · exact hn0 he.symm
  · exact hn1 he.symm

theorem no_clean_missing_pair (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) :
    ∀s∈f.F,¬s⊆h.clean := by
  intro s hs hsC
  obtain ⟨x,y,hxy,hsxy⟩ := Finset.card_eq_two.mp (f.edge_card s hs)
  have hx : x∈h.clean := hsC (by rw [hsxy]; simp)
  have hy : y∈h.clean := hsC (by rw [hsxy]; simp)
  have hm : ({x,y}:Finset Coord)∈f.F := hsxy ▸ hs
  have hnot : ¬h.clean⊆s := by
    intro hh
    have hc := Finset.card_le_card hh
    rw [h.clean_card,f.edge_card s hs] at hc
    omega
  obtain ⟨z,hz,hzs⟩ := Finset.not_subset.mp hnot
  by_cases his : PairIsolated f.F z
  · exact h.missing_clean_and_isolated_false f x y z hx hy hxy hm hz his
  obtain ⟨t,hts,htF,hFt⟩ := pair_family_other_edge f.F s hFcard hs
  have hzt : z∈t := by
    by_contra hn
    apply his
    intro q hq hzq
    rw [hFt] at hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hzs hzq
    · exact hn (Finset.mem_singleton.mp hq ▸ hzq)
  have avoid (u v : Coord) (hu : u∉h.clean) (hv : v∉h.clean) : ({u,v}:Finset Coord)∉f.F := by
    intro huv
    rw [hFt] at huv
    rcases Finset.mem_insert.mp huv with he | he
    · exact hu (hsC (he ▸ (by simp : u∈({u,v}:Finset Coord))))
    · have he' := Finset.mem_singleton.mp he
      have hzuv : z∈({u,v}:Finset Coord) := he'.symm ▸ hzt
      rcases Finset.mem_insert.mp hzuv with rfl | hzuv
      · exact hu hz
      · exact hv (Finset.mem_singleton.mp hzuv ▸ hz)
  have hi := (mem_distinctR a b c d h.i).mp h.hi
  have hj := (mem_distinctR a b c d h.j).mp h.hj
  have ht : InPath p (triple a h.i h.j) :=
    (f.selected_iff h.i h.j h.hij hi.1 hi.2.1 hj.1 hj.2.1).mpr
      (avoid h.i h.j h.clean_avoids.1 h.clean_avoids.2.1)
  obtain ⟨w,hw,hadj⟩ := selected_has_neighbor_of_nontrivial p h.outer.nontrivial (triple a h.i h.j) ht
  obtain ⟨k,hka,hkb,hki,hkj,rfl⟩ := h.hole_neighbor_cover w hw hadj
  by_cases hkc : k=c
  · subst k
    rcases h.special_extension_missing f c (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc)
      (Ne.symm hi.2.2.1) (Ne.symm hj.2.2.1) ht hw with hm | hm
    · exact avoid c h.i h.clean_avoids.2.2.1 h.clean_avoids.1 hm
    · exact avoid c h.j h.clean_avoids.2.2.1 h.clean_avoids.2.1 hm
  by_cases hkd : k=d
  · subst k
    rcases h.special_extension_missing f d (Ne.symm h.outer.had) (Ne.symm h.outer.hbd)
      (Ne.symm hi.2.2.2) (Ne.symm hj.2.2.2) ht hw with hm | hm
    · exact avoid d h.i h.clean_avoids.2.2.2 h.clean_avoids.1 hm
    · exact avoid d h.j h.clean_avoids.2.2.2 h.clean_avoids.2.1 hm
  have hk : k∈h.clean := (h.mem_clean k).mpr ⟨(mem_distinctR _ _ _ _ _).mpr ⟨hka,hkb,hkc,hkd⟩,hki,hkj⟩
  have hh := h.extension_missing f k hk hw
  have heq (r : Coord) (hr : r∉h.clean) (hrk : ({r,k}:Finset Coord)∈f.F) : ({r,k}:Finset Coord)=t := by
    rw [hFt] at hrk
    rcases Finset.mem_insert.mp hrk with he | he
    · exact False.elim (hr (hsC (he ▸ (by simp : r∈({r,k}:Finset Coord)))))
    · exact Finset.mem_singleton.mp he
  have he : ({h.i,k}:Finset Coord)=({h.j,k}:Finset Coord) :=
    (heq h.i h.clean_avoids.1 hh.1).trans (heq h.j h.clean_avoids.2.1 hh.2).symm
  have him : h.i∈({h.j,k}:Finset Coord) := he ▸ (by simp : h.i∈({h.i,k}:Finset Coord))
  rcases Finset.mem_insert.mp him with he | he
  · exact h.hij he
  · exact hki (Finset.mem_singleton.mp he).symm

theorem middle_hole_forced (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) :
    ({h.i,h.j}:Finset Coord)∈f.F := by
  by_contra hn
  have hi := (mem_distinctR a b c d h.i).mp h.hi
  have hj := (mem_distinctR a b c d h.j).mp h.hj
  have ht : InPath p (triple a h.i h.j) :=
    (f.selected_iff h.i h.j h.hij hi.1 hi.2.1 hj.1 hj.2.1).mpr hn
  have hclean := h.no_clean_missing_pair f hFcard
  have noordinary (k : Coord) (hk : k∈h.clean) : ¬InPath p (quad a h.i h.j k) := by
    intro hq
    have hk' := (h.mem_clean k).mp hk
    have hm := h.extension_missing f k hk hq
    have hne : ({h.i,k}:Finset Coord)≠{h.j,k} := by
      intro he
      have hh : h.i∈({h.j,k}:Finset Coord) := he ▸ (by simp : h.i∈({h.i,k}:Finset Coord))
      rcases Finset.mem_insert.mp hh with hh | hh
      · exact h.hij hh
      · exact hk'.2.1 (Finset.mem_singleton.mp hh).symm
    have hFt := pair_family_eq_two_of_mem f.F {h.i,k} {h.j,k} hFcard hm.1 hm.2 hne
    obtain ⟨u,hinj,hu⟩ := fork_family_two_isolated h.clean f.F h.i h.j k h.clean_card
      h.clean_avoids.1 h.clean_avoids.2.1 hFt
    have hnl := h.two_clean_isolated_hole_not_low f u hinj hu ht
    have coordinate (s : Finset Coord) (hs : s∈f.F) (r : Coord) (hr : r∈s) :
        r=h.i ∨ r=h.j ∨ r=k := by
      rw [hFt] at hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · rcases Finset.mem_insert.mp hr with he | he
        · exact Or.inl he
        · exact Or.inr (Or.inr (Finset.mem_singleton.mp he))
      · have he := Finset.mem_singleton.mp hs
        rw [he] at hr
        rcases Finset.mem_insert.mp hr with he | he
        · exact Or.inr (Or.inl he)
        · exact Or.inr (Or.inr (Finset.mem_singleton.mp he))
    have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (triple a h.i h.j) w) :
        w=quad a h.i h.j k := by
      obtain ⟨r,hra,hrb,hri,hrj,rfl⟩ := h.hole_neighbor_cover w hw hadj
      have hm' := h.special_extension_missing f r hra hrb hri hrj ht hw
      have hr : r=h.i ∨ r=h.j ∨ r=k := by
        rcases hm' with hm' | hm'
        · exact coordinate _ hm' r (by simp)
        · exact coordinate _ hm' r (by simp)
      have hrk := hr.resolve_left hri |>.resolve_left hrj
      rw [hrk]
    apply hnl
    intro x y hx hy hax hay
    exact (unique x hx hax).trans (unique y hy hay).symm
  have cover : ∀w,InPath p w → Adj (triple a h.i h.j) w →
      w=quad a h.i h.j c ∨ w=quad a h.i h.j d := by
    intro w hw hadj
    obtain ⟨k,hka,hkb,hki,hkj,rfl⟩ := h.hole_neighbor_cover w hw hadj
    by_cases hkc : k=c
    · exact Or.inl (by rw [hkc])
    by_cases hkd : k=d
    · exact Or.inr (by rw [hkd])
    exact False.elim (noordinary k ((h.mem_clean k).mpr
      ⟨(mem_distinctR _ _ _ _ _).mpr ⟨hka,hkb,hkc,hkd⟩,hki,hkj⟩) hw)
  have special_count (s : Coord) (hs : s=c ∨ s=d) (hq : InPath p (quad a h.i h.j s)) :
      ∃u : Fin 2 → Coord,Function.Injective u ∧ ∀r,u r∈h.clean ∧ PairIsolated f.F (u r) := by
    have hsa : s≠a := fun hsa => hs.elim (fun he => h.outer.hac (hsa.symm.trans he)) (fun he => h.outer.had (hsa.symm.trans he))
    have hsb : s≠b := fun hsb => hs.elim (fun he => h.outer.hbc (hsb.symm.trans he)) (fun he => h.outer.hbd (hsb.symm.trans he))
    have hsi : s≠h.i := fun hsi => hs.elim (fun he => hi.2.2.1 (hsi.symm.trans he)) (fun he => hi.2.2.2 (hsi.symm.trans he))
    have hsj : s≠h.j := fun hsj => hs.elim (fun he => hj.2.2.1 (hsj.symm.trans he)) (fun he => hj.2.2.2 (hsj.symm.trans he))
    have hsC : s∉h.clean := by
      intro hsc
      rcases hs with he | he
      · exact h.clean_avoids.2.2.1 (by simpa only [he] using hsc)
      · exact h.clean_avoids.2.2.2 (by simpa only [he] using hsc)
    rcases h.special_extension_missing f s hsa hsb hsi hsj ht hq with hm | hm
    · exact outside_edge_two_isolated h.clean f.F h.clean_card hFcard f.edge_card hclean
        {s,h.i} hm (h.clean_pair_disjoint s h.i hsC h.clean_avoids.1)
    · exact outside_edge_two_isolated h.clean f.F h.clean_card hFcard f.edge_card hclean
        {s,h.j} hm (h.clean_pair_disjoint s h.j hsC h.clean_avoids.2.1)
  obtain ⟨w,hw,hadj⟩ := selected_has_neighbor_of_nontrivial p h.outer.nontrivial _ ht
  have two : ∃u : Fin 2 → Coord,Function.Injective u ∧ ∀r,u r∈h.clean ∧ PairIsolated f.F (u r) := by
    rcases cover w hw hadj with he | he
    · exact special_count c (Or.inl rfl) (he ▸ hw)
    · exact special_count d (Or.inr rfl) (he ▸ hw)
  obtain ⟨u,hinj,hu⟩ := two
  have hnl := h.two_clean_isolated_hole_not_low f u hinj hu ht
  have hq := force_two_neighbors p (triple a h.i h.j) (quad a h.i h.j c) (quad a h.i h.j d) hnl cover
  have hcm := h.special_extension_missing f c (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc)
    (Ne.symm hi.2.2.1) (Ne.symm hj.2.2.1) ht hq.1
  have hdm := h.special_extension_missing f d (Ne.symm h.outer.had) (Ne.symm h.outer.hbd)
    (Ne.symm hi.2.2.2) (Ne.symm hj.2.2.2) ht hq.2
  have finish (x y : Coord) (hx : x=h.i ∨ x=h.j) (hy : y=h.i ∨ y=h.j)
      (hcx : ({c,x}:Finset Coord)∈f.F) (hdy : ({d,y}:Finset Coord)∈f.F) : False := by
    have hxc : x∉h.clean := hx.elim (fun he => he ▸ h.clean_avoids.1) (fun he => he ▸ h.clean_avoids.2.1)
    have hyc : y∉h.clean := hy.elim (fun he => he ▸ h.clean_avoids.1) (fun he => he ▸ h.clean_avoids.2.1)
    have hcy : c≠y := hy.elim (fun he => he ▸ Ne.symm hi.2.2.1) (fun he => he ▸ Ne.symm hj.2.2.1)
    have hne : ({c,x}:Finset Coord)≠{d,y} := by
      intro he
      have hm : c∈({d,y}:Finset Coord) := he ▸ (by simp : c∈({c,x}:Finset Coord))
      rcases Finset.mem_insert.mp hm with he | he
      · exact h.outer.hcd he
      · exact hcy (Finset.mem_singleton.mp he)
    have hFt := pair_family_eq_two_of_mem f.F {c,x} {d,y} hFcard hcx hdy hne
    obtain ⟨z,hzinj,hz⟩ := two_outside_edges_three_isolated h.clean f.F {c,x} {d,y}
      h.clean_card hFt (h.clean_pair_disjoint c x h.clean_avoids.2.2.1 hxc)
      (h.clean_pair_disjoint d y h.clean_avoids.2.2.2 hyc)
    exact h.three_clean_isolated_false f z hzinj hz
  rcases hcm with hcm | hcm <;> rcases hdm with hdm | hdm
  · exact finish h.i h.i (Or.inl rfl) (Or.inl rfl) hcm hdm
  · exact finish h.i h.j (Or.inl rfl) (Or.inr rfl) hcm hdm
  · exact finish h.j h.i (Or.inr rfl) (Or.inl rfl) hcm hdm
  · exact finish h.j h.j (Or.inr rfl) (Or.inr rfl) hcm hdm

end EqualOuterPairConfig
#print axioms EqualOuterPairConfig.no_clean_missing_pair
#print axioms EqualOuterPairConfig.middle_hole_forced
end
end Snake9
