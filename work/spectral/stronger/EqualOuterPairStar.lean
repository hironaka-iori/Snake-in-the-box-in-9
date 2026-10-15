import EqualOuterPairIncident

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

namespace EqualOuterPairConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : EqualOuterPairConfig p a b c d)
include h

theorem ordinary_saturation (f : MissingAtNeighbor p a b) (k r s : Coord)
    (hk : k∈h.clean) (hr : r∈distinctR a b c d) (hrk : r≠k)
    (hsa : s≠a) (hsb : s≠b)
    (hRR : ∀r,r∈distinctR a b c d → r≠k → ({k,r}:Finset Coord)∉f.F) :
    ¬InPath p (quad a k r s) := by
  have hh := (mem_distinctR a b c d k).mp ((h.mem_clean k).mp hk).1
  have hh' := (mem_distinctR a b c d r).mp hr
  have hs := h.clean_corners k r hk hr (Ne.symm hrk)
  have ht := (f.selected_iff k r (Ne.symm hrk) hh.1 hh.2.1 hh'.1 hh'.2.1).mpr
    (hRR r hr hrk)
  exact two_layer_saturation p a b k r s h.outer.hab hsa hsb hs.1 hs.2 ht

theorem ordinary_c_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈h.clean) (hRR : ∀r,r∈distinctR a b c d → r≠k → ({k,r}:Finset Coord)∉f.F)
    (hnc : ¬InPath p (pair c k)) :
    ∀w, InPath p w → Adj (triple a c k) w →
      w=quad a b c k ∨ w=quad a c d k := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp ((h.mem_clean k).mp hk).1
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_triple a c k hadj
  by_cases hra : r=a
  · subst r; rw [quad_cancel_first] at hw; exact False.elim (hnc hw)
  by_cases hrc : r=c
  · subst r; rw [quad_cancel_second] at hw
    exact False.elim (h.absent_pair_a k hka hkb hw)
  by_cases hrk : r=k
  · subst r; rw [quad_cancel_third] at hw
    exact False.elim (h.absent_pair_a c (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hw)
  by_cases hrb : r=b
  · subst r; left; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  by_cases hrd : r=d
  · subst r; right; exact quad_swap_last _ _ _ _
  apply False.elim (h.ordinary_saturation f k r c hk
    ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩) hrk
    (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hRR _)
  have he : quad a c k r=quad a k r c := by
    apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  exact he ▸ hw

theorem missing_d_pair_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈h.clean) (hm : ({d,k}:Finset Coord)∈f.F) :
    ∀w, InPath p w → Adj (pair d k) w → w=triple b d k ∨ w=triple c d k := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp ((h.mem_clean k).mp hk).1
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_pair d k hadj
  by_cases hrd : r=d
  · subst r; rw [triple_cancel_left] at hw
    exact False.elim (h.outer.absent_unit k hka hkc hw)
  by_cases hrk : r=k
  · subst r; rw [triple_cancel_right] at hw
    exact False.elim (h.outer.absent_unit d (Ne.symm h.outer.had) (Ne.symm h.outer.hcd) hw)
  by_cases hra : r=a
  · subst r; rw [triple_rotate] at hw
    exact False.elim ((f.selected_iff d k (Ne.symm hkd) (Ne.symm h.outer.had)
      (Ne.symm h.outer.hbd) hka hkb).mp hw hm)
  by_cases hrb : r=b
  · subst r; left; exact triple_rotate _ _ _
  by_cases hrc : r=c
  · subst r; right; exact triple_rotate _ _ _
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  exact False.elim (selected_triple_forbidden p d k r (Ne.symm hkd) (Ne.symm hrd)
    (Ne.symm hrk) (h.side_pair k ((h.mem_clean k).mp hk).1) (h.side_pair r hr)
    (h.clean_corners k r hk hr (Ne.symm hrk)).1 hw)

theorem star_d_middle_impossible (f : MissingAtNeighbor p a b) (k u v : Coord)
    (hk : k∈h.clean) (hu : u∈h.clean) (hv : v∈h.clean) (huv : u≠v)
    (hU : ∀s∈f.F,u∉s) (hV : ∀s∈f.F,v∉s)
    (hF : f.F={{h.i,h.j},{d,k}}) : False := by
  obtain ⟨hkR,hki,hkj⟩ := (h.mem_clean k).mp hk
  have huR := ((h.mem_clean u).mp hu).1
  have hvR := ((h.mem_clean v).mp hv).1
  have hi := (mem_distinctR a b c d h.i).mp h.hi
  have hj := (mem_distinctR a b c d h.j).mp h.hj
  have hh := (mem_distinctR a b c d k).mp hkR
  have hhu := (mem_distinctR a b c d u).mp huR
  have hhv := (mem_distinctR a b c d v).mp hvR
  have hdkF : ({d,k}:Finset Coord)∈f.F := by rw [hF]; simp
  have hku : k≠u := by intro he; exact hU _ hdkF (by simp [←he])
  have hkv : k≠v := by intro he; exact hV _ hdkF (by simp [←he])
  have hcF : ({c,k}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ (Ne.symm hi.2.2.1) (Ne.symm hj.2.2.1),
      delta_pair_ne _ _ _ _ h.outer.hcd (Ne.symm hh.2.2.1)⟩
  have hcdF : ({c,d}:Finset Coord)∉f.F := by
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ (Ne.symm hi.2.2.1) (Ne.symm hj.2.2.1),
      delta_pair_ne _ _ _ _ h.outer.hcd (Ne.symm hh.2.2.1)⟩
  have hRR : ∀r,r∈distinctR a b c d → r≠k → ({k,r}:Finset Coord)∉f.F := by
    intro r hr hrk
    have hhr := (mem_distinctR a b c d r).mp hr
    rw [hF]; simp only [mem_insert,mem_singleton,not_or]
    exact ⟨delta_pair_ne _ _ _ _ hki hkj,delta_pair_ne_right _ _ _ _ hhr.2.2.2 hrk⟩
  have hck := (f.selected_iff c k (Ne.symm hh.2.2.1) (Ne.symm h.outer.hac)
    (Ne.symm h.outer.hbc) hh.1 hh.2.1).mpr hcF
  have hcd := (f.selected_iff c d h.outer.hcd (Ne.symm h.outer.hac)
    (Ne.symm h.outer.hbc) (Ne.symm h.outer.had) (Ne.symm h.outer.hbd)).mpr hcdF
  have hnb := h.nonlow_outside_two f u v hu hv huv hU hV (pair b k) (h.row_selected k hkR)
    (by simp [bit_pair,Ne.symm hhu.2.1,hku]) (by simp [bit_pair,Ne.symm hhv.2.1,hkv])
  have hnc := h.nonlow_outside_two f u v hu hv huv hU hV (triple a c k) hck
    (by simp [bit_triple,Ne.symm hhu.1,Ne.symm hhu.2.2.1,hku])
    (by simp [bit_triple,Ne.symm hhv.1,Ne.symm hhv.2.2.1,hkv])
  have hnd := h.nonlow_outside_two f u v hu hv huv hU hV (pair d k) (h.side_pair k hkR)
    (by simp [bit_pair,Ne.symm hhu.2.2.2,hku]) (by simp [bit_pair,Ne.symm hhv.2.2.2,hkv])
  have hbkc := (force_two_neighbors p (pair b k) (triple b k c) (triple b k d) hnb
    (h.toLocal.row_cover k hkR hk (h.row_selected k hkR))).1
  have hnck : ¬InPath p (pair c k) := by
    intro hs
    have adj1 : Adj (pair c k) (triple a c k) := by
      rw [←triple_rotate c k a]; exact pair_triple_adj _ _ _
    have adj2 : Adj (pair c k) (triple b k c) := by
      have he : triple b k c=triple c k b := by apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
      rw [he]; exact pair_triple_adj _ _ _
    rcases selected_three_neighbors_repeat p hs h.outer.hc hck hbkc
      (adj_symmetric (unit_pair_adj _ _)) adj1 adj2 with he | he | he
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_unit,bit_triple,Ne.symm h.outer.hac,hh.1] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit b.val) he
      simp [bit_unit,bit_triple,Ne.symm h.outer.hbc,hh.2.1] at hb
    · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
      simp [bit_triple,Ne.symm h.outer.hab,Ne.symm h.outer.hac,hh.1] at hb
  have hq := (force_two_neighbors p (triple a c k) (quad a b c k) (quad a c d k)
    hnc (h.ordinary_c_cover f k hk hRR hnck)).2
  have hcdk := (force_two_neighbors p (pair d k) (triple b d k) (triple c d k)
    hnd (h.missing_d_pair_cover f k hk hdkF)).2
  have hno := ordinary_quad_absent p c a d k (Ne.symm h.outer.hac)
    (Ne.symm h.outer.had) hh.1 (Ne.symm hh.2.2.2)
    (by simpa only [triple,pair_comm c a] using hcd)
    (by simpa only [triple,pair_comm c a] using hck) hcdk
  apply hno
  simpa only [quad_swap_first a c d k] using hq

theorem star_c_middle_impossible (f : MissingAtNeighbor p a b) (k u v : Coord)
    (hk : k∈h.clean) (hu : u∈h.clean) (hv : v∈h.clean) (huv : u≠v)
    (hU : ∀s∈f.F,u∉s) (hV : ∀s∈f.F,v∉s)
    (hF : f.F={{h.i,h.j},{c,k}}) : False :=
  h.mirror.star_d_middle_impossible f.mirror k u v (h.mirror_clean k hk)
    (h.mirror_clean u hu) (h.mirror_clean v hv) huv hU hV hF

def swapHole : EqualOuterPairConfig p a b c d where
  outer := h.outer
  i := h.j
  j := h.i
  hi := h.hj
  hj := h.hi
  hij := Ne.symm h.hij
  left_eq := by simpa only [Finset.pair_comm h.j h.i] using h.left_eq
  right_eq := by simpa only [Finset.pair_comm h.j h.i] using h.right_eq

theorem swapHole_clean (k : Coord) (hk : k∈h.clean) : k∈h.swapHole.clean := by
  obtain ⟨hkR,hki,hkj⟩ := (h.mem_clean k).mp hk
  exact (h.swapHole.mem_clean k).mpr ⟨hkR,hkj,hki⟩

theorem incident_j_middle_impossible (f : MissingAtNeighbor p a b) (k u v : Coord)
    (hk : k∈h.clean) (hu : u∈h.clean) (hv : v∈h.clean) (huv : u≠v)
    (hU : ∀s∈f.F,u∉s) (hV : ∀s∈f.F,v∉s)
    (hF : f.F={{h.i,h.j},{h.j,k}}) : False := by
  apply h.swapHole.incident_middle_impossible f k u v (h.swapHole_clean k hk)
    (h.swapHole_clean u hu) (h.swapHole_clean v hv) huv hU hV
  simpa only [swapHole,Finset.pair_comm h.j h.i] using hF

end EqualOuterPairConfig
#print axioms EqualOuterPairConfig.star_d_middle_impossible
#print axioms EqualOuterPairConfig.star_c_middle_impossible
#print axioms EqualOuterPairConfig.incident_j_middle_impossible
end
end Snake9
