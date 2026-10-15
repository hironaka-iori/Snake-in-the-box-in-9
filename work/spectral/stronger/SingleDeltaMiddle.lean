import SingleDeltaBase

namespace Snake9
open Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

namespace SingleDeltaConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SingleDeltaConfig p a b c d)
include h

theorem ck_resource_cover (f : MissingAtNeighbor p a b)
    (ht : InPath p (triple a c h.k)) :
    ∀w,InPath p w → Adj (triple a c h.k) w →
      ∃s∈f.F,SingleDeltaResource c d h.k s ∧ SingleDeltaResourceUse a c d h.k w s := by
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_triple a c h.k hadj
  by_cases hra : r=a
  · subst r; rw [quad_cancel_first] at hw
    exact False.elim (h.absent_pair_c h.k h.hk.2.2.1 h.hk.2.1 hw)
  by_cases hrc : r=c
  · subst r; rw [quad_cancel_second] at hw
    exact False.elim (h.absent_pair_a h.k h.hk.1 h.hk.2.1 hw)
  by_cases hrk : r=h.k
  · rw [hrk,quad_cancel_third] at hw
    exact False.elim (h.absent_pair_a c (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hw)
  by_cases hrb : r=b
  · subst r
    have he : quad a c h.k b=quad a b c h.k := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    have hn := (h.outer.right_pair_iff c h.k (Ne.symm h.hk.2.2.1)
      (Ne.symm h.outer.hbc) h.outer.hcd h.hk.2.1 h.hk.2.2.2).mp (he ▸ hw)
    exact False.elim (hn (by rw [h.right_eq]; simp))
  by_cases hrd : r=d
  · subst r
    have hh : ({c,d}:Finset Coord)∈f.F ∨ ({d,h.k}:Finset Coord)∈f.F := by
      by_contra hn
      push_neg at hn
      have htcd := (f.selected_iff c d h.outer.hcd (Ne.symm h.outer.hac)
        (Ne.symm h.outer.hbc) (Ne.symm h.outer.had) (Ne.symm h.outer.hbd)).mpr hn.1
      have htdk := (f.selected_iff d h.k (Ne.symm h.hk.2.2.2) (Ne.symm h.outer.had)
        (Ne.symm h.outer.hbd) h.hk.1 h.hk.2.1).mpr hn.2
      exact ordinary_quad_absent p a c h.k d h.outer.hac h.hk.2.2.1
        (Ne.symm h.outer.hcd) h.hk.2.2.2 ht htcd
        (by simpa only [triple_swap a d h.k] using htdk) hw
    rcases hh with hh | hh
    · exact ⟨{c,d},hh,Or.inr rfl,Or.inl ⟨rfl,Or.inl rfl⟩⟩
    · exact ⟨{d,h.k},hh,Or.inl (by simp),Or.inl ⟨rfl,Or.inr rfl⟩⟩
  have hkr : ({h.k,r}:Finset Coord)∈f.F := by
    by_contra hn
    have htr := (f.selected_iff h.k r (Ne.symm hrk) h.hk.1 h.hk.2.1 hra hrb).mpr hn
    have hs := h.selected_outer_k r hra hrb hrc hrd hrk
    apply h.saturated_outer h.k r c h.hk.1 h.hk.2.1 hra hrb
      (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hs.1 hs.2 htr
    have he : quad a c h.k r=quad a h.k r c := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact he ▸ hw
  exact ⟨{h.k,r},hkr,Or.inl (by simp),Or.inr ⟨r,hrc,hrd,hrk,rfl,rfl⟩⟩

theorem ij_neighbor_cover :
    ∀w,InPath p w → Adj (triple a h.i h.j) w →
      ∃r,r≠a ∧ r≠b ∧ r≠h.i ∧ r≠h.j ∧ w=quad a h.i h.j r := by
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_triple a h.i h.j hadj
  by_cases hra : r=a
  · subst r; rw [quad_cancel_first] at hw
    have hn := (h.outer.left.selected_iff h.i h.j h.hij h.hi.1 h.hi.2.2.1 h.hj.1 h.hj.2.2.1).mp hw
    exact False.elim (hn (by rw [h.left_eq]; simp))
  by_cases hri : r=h.i
  · rw [hri,quad_cancel_second] at hw
    exact False.elim (h.absent_pair_a h.j h.hj.1 h.hj.2.1 hw)
  by_cases hrj : r=h.j
  · rw [hrj,quad_cancel_third] at hw
    exact False.elim (h.absent_pair_a h.i h.hi.1 h.hi.2.1 hw)
  by_cases hrb : r=b
  · subst r
    have he : quad a h.i h.j b=quad a b h.i h.j := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    have hn := (h.outer.right_pair_iff h.i h.j h.hij h.hi.2.1 h.hi.2.2.2 h.hj.2.1 h.hj.2.2.2).mp (he ▸ hw)
    exact False.elim (hn (by rw [h.right_eq]; simp))
  exact ⟨r,hra,hrb,hri,hrj,rfl⟩

theorem ij_ordinary_missing (f : MissingAtNeighbor p a b) (r : Coord)
    (hra : r≠a) (hrb : r≠b) (hrc : r≠c) (hrd : r≠d) (hri : r≠h.i) (hrj : r≠h.j)
    (hq : InPath p (quad a h.i h.j r)) :
    ({h.i,r}:Finset Coord)∈f.F ∧ ({h.j,r}:Finset Coord)∈f.F := by
  constructor
  · by_contra hn
    have ht := (f.selected_iff h.i r (Ne.symm hri) h.hi.1 h.hi.2.1 hra hrb).mpr hn
    have hs := h.selected_outer_i r hra hrb hrc hrd hri hrj
    apply h.saturated_outer h.i r h.j h.hi.1 h.hi.2.1 hra hrb h.hj.1 h.hj.2.1 hs.1 hs.2 ht
    simpa only [quad_swap_last a h.i h.j r] using hq
  · by_contra hn
    have ht := (f.selected_iff h.j r (Ne.symm hrj) h.hj.1 h.hj.2.1 hra hrb).mpr hn
    have hs := h.selected_outer_j r hra hrb hrc hrd hri hrj
    apply h.saturated_outer h.j r h.i h.hj.1 h.hj.2.1 hra hrb h.hi.1 h.hi.2.1 hs.1 hs.2 ht
    have he : quad a h.i h.j r=quad a h.j r h.i := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact he ▸ hq

theorem ij_special_missing (f : MissingAtNeighbor p a b) (r : Coord)
    (hra : r≠a) (hrb : r≠b) (hri : r≠h.i) (hrj : r≠h.j)
    (ht : InPath p (triple a h.i h.j)) (hq : InPath p (quad a h.i h.j r)) :
    ({r,h.i}:Finset Coord)∈f.F ∨ ({r,h.j}:Finset Coord)∈f.F := by
  by_contra hn
  push_neg at hn
  have hti := (f.selected_iff r h.i hri hra hrb h.hi.1 h.hi.2.1).mpr hn.1
  have htj := (f.selected_iff r h.j hrj hra hrb h.hj.1 h.hj.2.1).mpr hn.2
  exact ordinary_quad_absent p a h.i h.j r (Ne.symm h.hi.1) (Ne.symm h.hij)
    hri (Ne.symm hrj) ht (by simpa only [triple_swap a r h.i] using hti)
    (by simpa only [triple_swap a r h.j] using htj) hq

theorem all_k_resources_force_ij_low (f : MissingAtNeighbor p a b)
    (hall : ∀s∈f.F,SingleDeltaResource c d h.k s)
    (ht : InPath p (triple a h.i h.j)) : AtMostOneNeighbor p (triple a h.i h.j) := by
  have absent (x y : Coord) (hxk : x≠h.k) (hyk : y≠h.k)
      (hne : ({x,y}:Finset Coord)≠{c,d}) : ({x,y}:Finset Coord)∉f.F := by
    intro hm
    rcases hall _ hm with hk | he
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      exact hk.elim (Ne.symm hxk) (Ne.symm hyk)
    · exact hne he
  have hci := absent c h.i (Ne.symm h.hk.2.2.1) h.hik
    (delta_pair_ne_right c h.i c d h.hi.2.2.1 h.hi.2.2.2)
  have hcj := absent c h.j (Ne.symm h.hk.2.2.1) h.hjk
    (delta_pair_ne_right c h.j c d h.hj.2.2.1 h.hj.2.2.2)
  have hdi := absent d h.i (Ne.symm h.hk.2.2.2) h.hik
    (delta_pair_ne_right d h.i c d h.hi.2.2.1 h.hi.2.2.2)
  have hdj := absent d h.j (Ne.symm h.hk.2.2.2) h.hjk
    (delta_pair_ne_right d h.j c d h.hj.2.2.1 h.hj.2.2.2)
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (triple a h.i h.j) w) : w=quad a h.i h.j h.k := by
    obtain ⟨r,hra,hrb,hri,hrj,rfl⟩ := h.ij_neighbor_cover w hw hadj
    by_cases hrc : r=c
    · subst r
      exact False.elim ((h.ij_special_missing f c hra hrb hri hrj ht hw).elim hci hcj)
    by_cases hrd : r=d
    · subst r
      exact False.elim ((h.ij_special_missing f d hra hrb hri hrj ht hw).elim hdi hdj)
    have hm := (h.ij_ordinary_missing f r hra hrb hrc hrd hri hrj hw).1
    have hrk : r=h.k := by
      rcases hall _ hm with hk | he
      · simp only [Finset.mem_insert,Finset.mem_singleton] at hk
        exact (hk.resolve_left (Ne.symm h.hik)).symm
      · exact False.elim (delta_pair_ne h.i r c d h.hi.2.2.1 h.hi.2.2.2 he)
    rw [hrk]
  intro x y hx hy hax hay
  exact (unique x hx hax).trans (unique y hy hay).symm

theorem middle_ck_missing (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2)
    (nonlow : ∀x y,x≠a → y≠a → InPath p (triple a x y) → ¬AtMostOneNeighbor p (triple a x y)) :
    ({c,h.k}:Finset Coord)∈f.F := by
  by_contra hn
  have ht := (f.selected_iff c h.k (Ne.symm h.hk.2.2.1) (Ne.symm h.outer.hac)
    (Ne.symm h.outer.hbc) h.hk.1 h.hk.2.1).mpr hn
  have hall := two_neighbors_exhaust_resources p f.F hFcard (triple a c h.k)
    (nonlow c h.k (Ne.symm h.outer.hac) h.hk.1 ht)
    (SingleDeltaResource c d h.k) (SingleDeltaResourceUse a c d h.k)
    (h.ck_resource_cover f ht)
    (fun w z s => single_delta_resource_use_unique a c d h.k h.hk.2.2.1 h.hk.2.2.2 w z s)
  have hijn : ({h.i,h.j}:Finset Coord)∉f.F := by
    intro hm
    rcases hall _ hm with hk | he
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      exact hk.elim (Ne.symm h.hik) (Ne.symm h.hjk)
    · exact delta_pair_ne h.i h.j c d h.hi.2.2.1 h.hi.2.2.2 he
  have htij := (f.selected_iff h.i h.j h.hij h.hi.1 h.hi.2.1 h.hj.1 h.hj.2.1).mpr hijn
  exact nonlow h.i h.j h.hi.1 h.hj.1 htij (h.all_k_resources_force_ij_low f hall htij)

theorem two_members_determine (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2)
    (s t : Finset Coord) (hs : s∈f.F) (ht : t∈f.F) (hst : s≠t) : f.F={s,t} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact hs
    · exact ht
  · simpa [hst] using hFcard.le

theorem middle_ij_missing (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2)
    (nonlow : ∀x y,x≠a → y≠a → InPath p (triple a x y) → ¬AtMostOneNeighbor p (triple a x y)) :
    ({h.i,h.j}:Finset Coord)∈f.F := by
  have hck := h.middle_ck_missing f hFcard nonlow
  by_contra hn
  have ht := (f.selected_iff h.i h.j h.hij h.hi.1 h.hi.2.1 h.hj.1 h.hj.2.1).mpr hn
  have hcvr : ∀w,InPath p w → Adj (triple a h.i h.j) w →
      w=quad a h.i h.j c ∨ w=quad a h.i h.j d := by
    intro w hw hadj
    obtain ⟨r,hra,hrb,hri,hrj,rfl⟩ := h.ij_neighbor_cover w hw hadj
    by_cases hrc : r=c
    · exact Or.inl (congrArg (quad a h.i h.j) hrc)
    by_cases hrd : r=d
    · exact Or.inr (congrArg (quad a h.i h.j) hrd)
    have hh := h.ij_ordinary_missing f r hra hrb hrc hrd hri hrj hw
    have hF := h.two_members_determine f hFcard {h.i,r} {h.j,r} hh.1 hh.2
      (delta_pair_ne h.i r h.j r h.hij (Ne.symm hri))
    rw [hF] at hck
    simp only [Finset.mem_insert,Finset.mem_singleton] at hck
    exact False.elim (hck.elim
      (delta_pair_ne c h.k h.i r (Ne.symm h.hi.2.2.1) (Ne.symm hrc))
      (delta_pair_ne c h.k h.j r (Ne.symm h.hj.2.2.1) (Ne.symm hrc)))
  have hs := force_two_neighbors p (triple a h.i h.j) (quad a h.i h.j c) (quad a h.i h.j d)
    (nonlow h.i h.j h.hi.1 h.hj.1 ht) hcvr
  have hc := h.ij_special_missing f c (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc)
    (Ne.symm h.hi.2.2.1) (Ne.symm h.hj.2.2.1) ht hs.1
  have hd := h.ij_special_missing f d (Ne.symm h.outer.had) (Ne.symm h.outer.hbd)
    (Ne.symm h.hi.2.2.2) (Ne.symm h.hj.2.2.2) ht hs.2
  have finish (x : Coord) (hxc : x≠c) (hxd : x≠d) (hxk : x≠h.k)
      (hx : ({c,x}:Finset Coord)∈f.F) : False := by
    have hF := h.two_members_determine f hFcard {c,h.k} {c,x} hck hx
      (delta_pair_ne_right c h.k c x h.hk.2.2.1 (Ne.symm hxk))
    rw [hF] at hd
    simp only [Finset.mem_insert,Finset.mem_singleton] at hd
    rcases hd with (he | he) | (he | he)
    · exact delta_pair_ne d h.i c h.k (Ne.symm h.outer.hcd) (Ne.symm h.hk.2.2.2) he
    · exact delta_pair_ne d h.i c x (Ne.symm h.outer.hcd) (Ne.symm hxd) he
    · exact delta_pair_ne d h.j c h.k (Ne.symm h.outer.hcd) (Ne.symm h.hk.2.2.2) he
    · exact delta_pair_ne d h.j c x (Ne.symm h.outer.hcd) (Ne.symm hxd) he
  exact hc.elim (finish h.i h.hi.2.2.1 h.hi.2.2.2 h.hik)
    (finish h.j h.hj.2.2.1 h.hj.2.2.2 h.hjk)

theorem middle_impossible (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2)
    (nonlow : ∀x y,x≠a → y≠a → InPath p (triple a x y) → ¬AtMostOneNeighbor p (triple a x y)) : False := by
  have hck := h.middle_ck_missing f hFcard nonlow
  have hij := h.middle_ij_missing f hFcard nonlow
  have hF := h.two_members_determine f hFcard {c,h.k} {h.i,h.j} hck hij
    (delta_pair_ne c h.k h.i h.j (Ne.symm h.hi.2.2.1) (Ne.symm h.hj.2.2.1))
  obtain ⟨zs,hzs,_⟩ := exists_two_coords_outside_seven a b c d h.i h.j h.k
  let z := zs 0
  obtain ⟨hza,hzb,hzc,hzd,hzi,hzj,hzk⟩ := hzs 0
  change z≠a at hza
  change z≠b at hzb
  change z≠c at hzc
  change z≠d at hzd
  change z≠h.i at hzi
  change z≠h.j at hzj
  change z≠h.k at hzk
  have hzmiss (r : Coord) : ({z,r}:Finset Coord)∉f.F := by
    rw [hF]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨delta_pair_ne z r c h.k hzc hzk,delta_pair_ne z r h.i h.j hzi hzj⟩
  have ht : InPath p (triple a c z) := by
    apply (f.selected_iff c z (Ne.symm hzc) (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hza hzb).mpr
    simpa only [Finset.pair_comm z c] using hzmiss c
  have hcdmiss : ({c,d}:Finset Coord)∉f.F := by
    rw [hF]
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨delta_pair_ne_right c d c h.k (Ne.symm h.outer.hcd) (Ne.symm h.hk.2.2.2),
      delta_pair_ne c d h.i h.j (Ne.symm h.hi.2.2.1) (Ne.symm h.hj.2.2.1)⟩
  have htcd := (f.selected_iff c d h.outer.hcd (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc)
    (Ne.symm h.outer.had) (Ne.symm h.outer.hbd)).mpr hcdmiss
  have htdz : InPath p (triple a d z) := by
    apply (f.selected_iff d z (Ne.symm hzd) (Ne.symm h.outer.had) (Ne.symm h.outer.hbd) hza hzb).mpr
    simpa only [Finset.pair_comm z d] using hzmiss d
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (triple a c z) w) : w=quad a b c z := by
    obtain ⟨r,rfl⟩ := neighbor_triple a c z hadj
    by_cases hra : r=a
    · subst r; rw [quad_cancel_first] at hw
      exact False.elim (h.absent_pair_c z hzc hzb hw)
    by_cases hrc : r=c
    · subst r; rw [quad_cancel_second] at hw
      exact False.elim (h.absent_pair_a z hza hzb hw)
    by_cases hrz : r=z
    · subst r; rw [quad_cancel_third] at hw
      exact False.elim (h.absent_pair_a c (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hw)
    by_cases hrb : r=b
    · subst r
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    by_cases hrd : r=d
    · subst r
      exact False.elim (ordinary_quad_absent p a c z d h.outer.hac hzc
        (Ne.symm h.outer.hcd) hzd ht htcd (by simpa only [triple_swap a d z] using htdz) hw)
    have hp : InPath p (pair z r) := by
      apply (h.outer.left.selected_iff z r (Ne.symm hrz) hza hzc hra hrc).mpr
      rw [h.left_eq]
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨delta_pair_ne z r b d hzb hzd,delta_pair_ne z r h.i h.j hzi hzj⟩
    have hq : InPath p (quad a b z r) := by
      apply (h.outer.right_pair_iff z r (Ne.symm hrz) hzb hzd hrb hrd).mpr
      rw [h.right_eq]
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨delta_pair_ne z r h.i h.j hzi hzj,delta_pair_ne z r c h.k hzc hzk⟩
    have htr := (f.selected_iff z r (Ne.symm hrz) hza hzb hra hrb).mpr (hzmiss r)
    apply False.elim
    apply h.saturated_outer z r c hza hzb hra hrb (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hp hq htr
    have he : quad a c z r=quad a z r c := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact he ▸ hw
  apply nonlow c z (Ne.symm h.outer.hac) hza ht
  intro w v hw hv hadjw hadjv
  exact (unique w hw hadjw).trans (unique v hv hadjv).symm

end SingleDeltaConfig
#print axioms SingleDeltaConfig.ck_resource_cover
#print axioms SingleDeltaConfig.middle_ij_missing
#print axioms SingleDeltaConfig.middle_impossible
end
end Snake9
