import OneTwoGeometry
import OneTwoBDCases
import ExtraFreshCoordinates

namespace Snake9
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

namespace OneTwoRoot
variable {m : Nat} {p : Snake m} {a b c d : Coord}
  (h : OneTwoRoot p a b c d) (f : TwoMissingAtNeighbor p a c)
include h f

theorem single_hole_alternative (e i : Coord) (s : Finset Coord)
    (hea : e≠a) (heb : e≠b) (hec : e≠c) (hed : e≠d)
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hid : i≠d) (hie : i≠e)
    (hF : f.F = {{b,e},s}) (hbs : b∉s)
    (hei : ({e,i} : Finset Coord) ∉ f.F)
    (hblock : ∀ j, ({i,j} : Finset Coord)=s → ¬ InPath p (quad a b i j)) :
    AtMostOneNeighbor p (triple a b i) ∨ AtMostOneNeighbor p (pair e i) := by
  have hbi : ({b,i} : Finset Coord) ∉ f.F := by
    rw [hF]
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rintro (he | he)
    · have hm : i∈({b,e} : Finset Coord) := he ▸ (by simp)
      simpa [hib,hie] using hm
    · exact hbs (he ▸ (by simp))
  have ht := h.selected_t f i hia hib hic hbi
  by_cases hn : AtMostOneNeighbor p (triple a b i)
  · exact Or.inl hn
  right
  obtain ⟨w,hw,hadj,hne⟩ := exists_neighbor_ne p (triple a b i) (quad a b c i) hn
  rcases h.triple_neighbor_cover_general i hia hib hic hid w hw hadj with he | ⟨j,hja,hjb,hjc,hji,he⟩
  · exact False.elim (hne he)
  have hq : InPath p (quad a b i j) := he ▸ hw
  have hje : j=e := by
    rcases h.connection_missing_or_hole f i j hia hib hic hja hjb hjc hji ht hq with hm | hm
    · rw [hF] at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · have hj : j∈({b,e} : Finset Coord) := hm ▸ (by simp)
        simpa [hjb] using hj
      · exact False.elim (hbs (hm ▸ (by simp)))
    · rw [hF] at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · have hb : b∈({i,j} : Finset Coord) := hm.symm ▸ (by simp)
        simp [Ne.symm hib,Ne.symm hjb] at hb
      · exact False.elim (hblock j hm hq)
  subst j
  have hai := (f.selected_iff e i (Ne.symm hie) hea hec hia hic).mpr hei
  apply h.hole_connection_low_degree e i hea heb hec hed hia hib hic hid (Ne.symm hie)
    _ ht hai
  simpa only [quad_swap_last a b i e] using hq

theorem single_hole_selected_t (e i : Coord) (s : Finset Coord)
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hie : i≠e)
    (hF : f.F = {{b,e},s}) (hbs : b∉s) : InPath p (triple a b i) := by
  apply h.selected_t f i hia hib hic
  rw [hF]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  rintro (he | he)
  · have hm : i∈({b,e} : Finset Coord) := he ▸ (by simp)
    simp [hib,hie] at hm
  · exact hbs (he ▸ (by simp))

theorem single_hole_free_alternative (e i : Coord) (s : Finset Coord)
    (hea : e≠a) (heb : e≠b) (hec : e≠c) (hed : e≠d)
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hid : i≠d) (hie : i≠e)
    (hF : f.F = {{b,e},s}) (hbs : b∉s) (his : i∉s) :
    AtMostOneNeighbor p (triple a b i) ∨ AtMostOneNeighbor p (pair e i) := by
  apply h.single_hole_alternative f e i s hea heb hec hed hia hib hic hid hie hF hbs
  · rw [hF]
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rintro (he | he)
    · have hb : b∈({e,i} : Finset Coord) := he.symm ▸ (by simp)
      simp [Ne.symm heb,Ne.symm hib] at hb
    · exact his (he ▸ (by simp))
  · intro j he
    exact False.elim (his (he ▸ (by simp)))

theorem two_holes_alternative (e g i : Coord)
    (hea : e≠a) (heb : e≠b) (hec : e≠c) (hed : e≠d)
    (hga : g≠a) (hgb : g≠b) (hgc : g≠c) (hgd : g≠d)
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hid : i≠d) (hie : i≠e) (hig : i≠g)
    (hF : f.F = {{b,e},{b,g}}) :
    AtMostOneNeighbor p (triple a b i) ∨
      AtMostOneNeighbor p (pair e i) ∨ AtMostOneNeighbor p (pair g i) := by
  have hbi : ({b,i} : Finset Coord) ∉ f.F := by
    rw [hF]
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rintro (he | he)
    · have hm : i∈({b,e} : Finset Coord) := he ▸ (by simp)
      simpa [hib,hie] using hm
    · have hm : i∈({b,g} : Finset Coord) := he ▸ (by simp)
      simpa [hib,hig] using hm
  have ht := h.selected_t f i hia hib hic hbi
  by_cases hn : AtMostOneNeighbor p (triple a b i)
  · exact Or.inl hn
  obtain ⟨w,hw,hadj,hne⟩ := exists_neighbor_ne p (triple a b i) (quad a b c i) hn
  rcases h.triple_neighbor_cover_general i hia hib hic hid w hw hadj with he | ⟨j,hja,hjb,hjc,hji,he⟩
  · exact False.elim (hne he)
  have hq : InPath p (quad a b i j) := he ▸ hw
  have hjeg : j=e ∨ j=g := by
    rcases h.connection_missing_or_hole f i j hia hib hic hja hjb hjc hji ht hq with hm | hm
    · rw [hF] at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · have hj : j∈({b,e} : Finset Coord) := hm ▸ (by simp)
        exact Or.inl (by simpa [hjb] using hj)
      · have hj : j∈({b,g} : Finset Coord) := hm ▸ (by simp)
        exact Or.inr (by simpa [hjb] using hj)
    · have hb : b∈({i,j} : Finset Coord) := by
        rw [hF] at hm
        simp only [Finset.mem_insert,Finset.mem_singleton] at hm
        rcases hm with hm | hm <;> exact hm.symm ▸ (by simp)
      simp [Ne.symm hib,Ne.symm hjb] at hb
  have hno (x : Coord) (hxb : x≠b) : ({x,i} : Finset Coord)∉f.F := by
    intro hm
    have hb : b∈({x,i} : Finset Coord) := by
      rw [hF] at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with hm | hm <;> exact hm.symm ▸ (by simp)
    simp [Ne.symm hxb,Ne.symm hib] at hb
  rcases hjeg with he | hg
  · subst j
    right; left
    have hai := (f.selected_iff e i (Ne.symm hie) hea hec hia hic).mpr (hno e heb)
    apply h.hole_connection_low_degree e i hea heb hec hed hia hib hic hid (Ne.symm hie)
      _ ht hai
    simpa only [quad_swap_last a b i e] using hq
  · subst j
    right; right
    have hai := (f.selected_iff g i (Ne.symm hig) hga hgc hia hic).mpr (hno g hgb)
    apply h.hole_connection_low_degree g i hga hgb hgc hgd hia hib hic hid (Ne.symm hig)
      _ ht hai
    simpa only [quad_swap_last a b i g] using hq

theorem be_two_holes_false (e g : Coord)
    (hea : e≠a) (heb : e≠b) (hec : e≠c) (hed : e≠d)
    (hga : g≠a) (hgb : g≠b) (hgc : g≠c) (hgd : g≠d)
    (hF : f.F = {{b,e},{b,g}}) : False := by
  obtain ⟨j,hj,hji⟩ := exists_three_coords_outside_six a b c d e g
  let v : Fin 3 → Fin 3 → Vertex := fun i r =>
    if r=0 then triple a b (j i) else if r=1 then pair e (j i) else pair g (j i)
  have hv : ∀ i r, InPath p (v i r) := by
    intro i r
    by_cases hr : r=0
    · simp only [v,hr,if_true]
      apply h.selected_t f (j i) (hj i).1 (hj i).2.1 (hj i).2.2.1
      rw [hF]
      simp only [Finset.mem_insert,Finset.mem_singleton]
      rintro (he | he)
      · have hm : j i∈({b,e} : Finset Coord) := he ▸ (by simp)
        simp [(hj i).2.1,(hj i).2.2.2.2.1] at hm
      · have hm : j i∈({b,g} : Finset Coord) := he ▸ (by simp)
        simp [(hj i).2.1,(hj i).2.2.2.2.2] at hm
    · simp only [v,hr,if_false]
      by_cases hr1 : r=1
      · rw [if_pos hr1]
        apply h.selected_pair e (j i) (Ne.symm (hj i).2.2.2.2.1) hea heb (hj i).1 (hj i).2.1
        simp [hec,hed]
      · rw [if_neg hr1]
        apply h.selected_pair g (j i) (Ne.symm (hj i).2.2.2.2.2) hga hgb (hj i).1 (hj i).2.1
        simp [hgc,hgd]
  have hdis : ∀ i l, i≠l → ∀ r s, v i r ≠ v l s := by
    intro i l hil r s he
    have hli : j l≠j i := fun he => hil (hji he).symm
    have hb := congrArg (fun z : Vertex => z.val.testBit (j i).val) he
    dsimp [v] at hb
    split_ifs at hb <;> simp [bit_pair,bit_triple,Ne.symm (hj i).1,Ne.symm (hj i).2.1,
      Ne.symm (hj i).2.2.2.2.1,Ne.symm (hj i).2.2.2.2.2,hli] at hb
  obtain ⟨i,hi⟩ := exists_good_group p v hv hdis
  have halt := h.two_holes_alternative f e g (j i) hea heb hec hed hga hgb hgc hgd
    (hj i).1 (hj i).2.1 (hj i).2.2.1 (hj i).2.2.2.1 (hj i).2.2.2.2.1 (hj i).2.2.2.2.2 hF
  rcases halt with ht | he | hg
  · exact hi 0 (by simpa [v] using ht)
  · exact hi 1 (by simpa [v] using he)
  · exact hi 2 (by simpa [v] using hg)

omit f in
theorem three_hole_groups_false (e : Coord)
    (hea : e≠a) (heb : e≠b) (hec : e≠c) (hed : e≠d)
    (j : Fin 3 → Coord) (hji : Function.Injective j)
    (hj : ∀i, j i≠a ∧ j i≠b ∧ j i≠c ∧ j i≠d ∧ j i≠e)
    (ht : ∀i, InPath p (triple a b (j i)))
    (halt : ∀i, AtMostOneNeighbor p (triple a b (j i)) ∨ AtMostOneNeighbor p (pair e (j i))) :
    False := by
  let v : Fin 3 → Fin 2 → Vertex := fun i r =>
    if r=0 then triple a b (j i) else pair e (j i)
  have hv : ∀i r, InPath p (v i r) := by
    intro i r
    by_cases hr : r=0
    · simpa [v,hr] using ht i
    · simp only [v,hr,if_false]
      apply h.selected_pair e (j i) (Ne.symm (hj i).2.2.2.2) hea heb (hj i).1 (hj i).2.1
      simp [hec,hed]
  have hdis : ∀ i l, i≠l → ∀ r s, v i r ≠ v l s := by
    intro i l hil r s he
    have hli : j l≠j i := fun he => hil (hji he).symm
    have hb := congrArg (fun z : Vertex => z.val.testBit (j i).val) he
    dsimp [v] at hb
    split_ifs at hb <;> simp [bit_pair,bit_triple,Ne.symm (hj i).1,Ne.symm (hj i).2.1,
      Ne.symm (hj i).2.2.2.2,hli] at hb
  obtain ⟨i,hi⟩ := exists_good_group p v hv hdis
  rcases halt i with hs | hs
  · exact hi 0 (by simpa [v] using hs)
  · exact hi 1 (by simpa [v] using hs)

omit f in
theorem two_hole_groups_extra_false (e x y : Coord)
    (hea : e≠a) (heb : e≠b) (hec : e≠c) (hed : e≠d)
    (j : Fin 2 → Coord) (hji : Function.Injective j)
    (hj : ∀i, j i≠a ∧ j i≠b ∧ j i≠c ∧ j i≠d ∧ j i≠e ∧ j i≠x ∧ j i≠y)
    (ht : ∀i, InPath p (triple a b (j i)))
    (halt : ∀i, AtMostOneNeighbor p (triple a b (j i)) ∨ AtMostOneNeighbor p (pair e (j i)))
    (hxy : InPath p (pair x y)) (hxyLow : AtMostOneNeighbor p (pair x y)) : False := by
  classical
  let v : Fin 2 → Vertex := fun i =>
    if AtMostOneNeighbor p (triple a b (j i)) then triple a b (j i) else pair e (j i)
  have hv : ∀i, InPath p (v i) := by
    intro i
    dsimp [v]
    split_ifs
    · exact ht i
    · apply h.selected_pair e (j i) (Ne.symm (hj i).2.2.2.2.1) hea heb (hj i).1 (hj i).2.1
      simp [hec,hed]
  have hl : ∀i, AtMostOneNeighbor p (v i) := by
    intro i
    dsimp [v]
    split_ifs with hh
    · exact hh
    · exact (halt i).resolve_left hh
  have hv01 : v 0≠v 1 := by
    intro he
    have h10 : j 1≠j 0 := fun he => by have hi := hji he; exact (by decide : (1:Fin 2)≠0) hi
    have hb := congrArg (fun z : Vertex => z.val.testBit (j 0).val) he
    dsimp [v] at hb
    split_ifs at hb <;> simp [bit_pair,bit_triple,Ne.symm (hj 0).1,Ne.symm (hj 0).2.1,
      Ne.symm (hj 0).2.2.2.2.1,h10] at hb
  have hvxy (i : Fin 2) : v i≠pair x y := by
    intro he
    have hb := congrArg (fun z : Vertex => z.val.testBit (j i).val) he
    dsimp [v] at hb
    split_ifs at hb <;> simp [bit_pair,bit_triple,Ne.symm (hj i).1,Ne.symm (hj i).2.1,
      Ne.symm (hj i).2.2.2.2.1,Ne.symm (hj i).2.2.2.2.2.1,Ne.symm (hj i).2.2.2.2.2.2] at hb
  rcases three_low_degree_vertices_repeat p (hv 0) (hv 1) hxy (hl 0) (hl 1) hxyLow with he | he | he
  · exact hv01 he
  · exact hvxy 0 he
  · exact hvxy 1 he

theorem be_nonb_false (e x y : Coord)
    (hea : e≠a) (heb : e≠b) (hec : e≠c) (hed : e≠d)
    (hxa : x≠a) (hxb : x≠b) (hxc : x≠c)
    (hya : y≠a) (hyb : y≠b) (hyc : y≠c) (hxy : x≠y)
    (hF : f.F = {{b,e},{x,y}}) : False := by
  have hbs : b∉({x,y} : Finset Coord) := by simp [Ne.symm hxb,Ne.symm hyb]
  have hgood (j : Fin 3 → Coord) (hji : Function.Injective j)
      (hj : ∀i, j i≠a ∧ j i≠b ∧ j i≠c ∧ j i≠d ∧ j i≠e ∧ j i≠x ∧ j i≠y) : False := by
    apply h.three_hole_groups_false e hea heb hec hed j hji
      (fun i => ⟨(hj i).1,(hj i).2.1,(hj i).2.2.1,(hj i).2.2.2.1,(hj i).2.2.2.2.1⟩)
    · intro i
      exact h.single_hole_selected_t f e (j i) {x,y} (hj i).1 (hj i).2.1
        (hj i).2.2.1 (hj i).2.2.2.2.1 hF hbs
    · intro i
      apply h.single_hole_free_alternative f e (j i) {x,y} hea heb hec hed
        (hj i).1 (hj i).2.1 (hj i).2.2.1 (hj i).2.2.2.1 (hj i).2.2.2.2.1 hF hbs
      simp [(hj i).2.2.2.2.2.1,(hj i).2.2.2.2.2.2]
  by_cases hxd : x=d
  · obtain ⟨j,hj,hji⟩ := exists_three_coords_outside_six a b c d e y
    apply hgood j hji
    intro i
    exact ⟨(hj i).1,(hj i).2.1,(hj i).2.2.1,(hj i).2.2.2.1,(hj i).2.2.2.2.1,
      by simpa [hxd] using (hj i).2.2.2.1,(hj i).2.2.2.2.2⟩
  by_cases hxe : x=e
  · obtain ⟨j,hj,hji⟩ := exists_three_coords_outside_six a b c d e y
    apply hgood j hji
    intro i
    exact ⟨(hj i).1,(hj i).2.1,(hj i).2.2.1,(hj i).2.2.2.1,(hj i).2.2.2.2.1,
      by simpa [hxe] using (hj i).2.2.2.2.1,(hj i).2.2.2.2.2⟩
  by_cases hyd : y=d
  · obtain ⟨j,hj,hji⟩ := exists_three_coords_outside_six a b c d e x
    apply hgood j hji
    intro i
    exact ⟨(hj i).1,(hj i).2.1,(hj i).2.2.1,(hj i).2.2.2.1,(hj i).2.2.2.2.1,
      (hj i).2.2.2.2.2,by simpa [hyd] using (hj i).2.2.2.1⟩
  by_cases hye : y=e
  · obtain ⟨j,hj,hji⟩ := exists_three_coords_outside_six a b c d e x
    apply hgood j hji
    intro i
    exact ⟨(hj i).1,(hj i).2.1,(hj i).2.2.1,(hj i).2.2.2.1,(hj i).2.2.2.2.1,
      (hj i).2.2.2.2.2,by simpa [hye] using (hj i).2.2.2.2.1⟩
  by_cases hq : InPath p (quad a b x y)
  · have htx := h.single_hole_selected_t f e x {x,y} hxa hxb hxc hxe hF hbs
    have hty := h.single_hole_selected_t f e y {x,y} hya hyb hyc hye hF hbs
    have haxy : ¬ InPath p (triple a x y) := by
      intro hs
      apply (f.selected_iff x y hxy hxa hxc hya hyc).mp hs
      rw [hF]; simp
    have hl := h.missing_connection_low_degree x y hxa hxb hxc hxd hya hyb hyc hxy hq htx hty haxy
    have hp : InPath p (pair x y) := by
      apply h.selected_pair x y hxy hxa hxb hya hyb
      simp [hxc,hxd]
    obtain ⟨j,hj,hji⟩ := exists_two_coords_outside_seven a b c d e x y
    apply h.two_hole_groups_extra_false e x y hea heb hec hed j hji hj _ _ hp hl
    · intro i
      exact h.single_hole_selected_t f e (j i) {x,y} (hj i).1 (hj i).2.1
        (hj i).2.2.1 (hj i).2.2.2.2.1 hF hbs
    · intro i
      apply h.single_hole_free_alternative f e (j i) {x,y} hea heb hec hed
        (hj i).1 (hj i).2.1 (hj i).2.2.1 (hj i).2.2.2.1 (hj i).2.2.2.2.1 hF hbs
      simp [(hj i).2.2.2.2.2.1,(hj i).2.2.2.2.2.2]
  · obtain ⟨j,hj,hji⟩ := exists_three_coords_outside_six a b c d e e
    apply h.three_hole_groups_false e hea heb hec hed j hji
      (fun i => ⟨(hj i).1,(hj i).2.1,(hj i).2.2.1,(hj i).2.2.2.1,(hj i).2.2.2.2.1⟩)
    · intro i
      exact h.single_hole_selected_t f e (j i) {x,y} (hj i).1 (hj i).2.1
        (hj i).2.2.1 (hj i).2.2.2.2.1 hF hbs
    · intro i
      apply h.single_hole_alternative f e (j i) {x,y} hea heb hec hed
        (hj i).1 (hj i).2.1 (hj i).2.2.1 (hj i).2.2.2.1 (hj i).2.2.2.2.1 hF hbs
      · rw [hF]
        simp only [Finset.mem_insert,Finset.mem_singleton]
        rintro (he | he)
        · have hb : b∈({e,j i} : Finset Coord) := he.symm ▸ (by simp)
          simp [Ne.symm heb,Ne.symm (hj i).2.1] at hb
        · have hee : e∈({x,y} : Finset Coord) := he ▸ (by simp)
          simp [Ne.symm hxe,Ne.symm hye] at hee
      · intro z he hz
        have hi : j i=x ∨ j i=y := by
          have hm : j i∈({x,y} : Finset Coord) := he ▸ (by simp)
          simpa using hm
        rcases hi with hix | hiy
        · have hzY : z=y := by
            have hm : y∈({j i,z} : Finset Coord) := he.symm ▸ (by simp)
            exact (by simpa [hix,Ne.symm hxy] using hm : y=z).symm
          apply hq
          simpa only [hix,hzY] using hz
        · have hzX : z=x := by
            have hm : x∈({j i,z} : Finset Coord) := he.symm ▸ (by simp)
            exact (by simpa [hiy,hxy] using hm : x=z).symm
          apply hq
          simpa only [hiy,hzX,quad_swap_last a b y x] using hz

end OneTwoRoot
#print axioms OneTwoRoot.single_hole_alternative
#print axioms OneTwoRoot.two_holes_alternative
#print axioms OneTwoRoot.be_nonb_false
end Snake9
