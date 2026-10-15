import EqualOuterPairEndpoints

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

namespace EqualOuterPairConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : EqualOuterPairConfig p a b c d)
include h

theorem incident_pair_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈h.clean) (hm : ({h.i,k}:Finset Coord)∈f.F) :
    ∀w,InPath p w → Adj (pair h.i k) w → w=triple h.i k c ∨ w=triple h.i k h.j := by
  obtain ⟨hkR,hki,hkj⟩ := (h.mem_clean k).mp hk
  have hi := (mem_distinctR a b c d h.i).mp h.hi
  have hj := (mem_distinctR a b c d h.j).mp h.hj
  have hh := (mem_distinctR a b c d k).mp hkR
  have hs : InPath p (pair h.i k) := by
    simpa only [pair_comm k h.i] using (h.clean_corners k h.i hk h.hi hki).1
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_pair h.i k hadj
  by_cases hri : r=h.i
  · rw [hri,triple_cancel_left] at hw
    exact False.elim (h.outer.absent_unit k hh.1 hh.2.2.1 hw)
  by_cases hrk : r=k
  · subst r; rw [triple_cancel_right] at hw
    exact False.elim (h.outer.absent_unit h.i hi.1 hi.2.2.1 hw)
  by_cases hra : r=a
  · subst r; rw [triple_rotate] at hw
    exact False.elim ((f.selected_iff h.i k (Ne.symm hki) hi.1 hi.2.1 hh.1 hh.2.1).mp hw hm)
  by_cases hrb : r=b
  · subst r; rw [triple_rotate] at hw
    exact False.elim (h.clean_b_absent k h.i hk h.hi hki (by simpa only [triple_swap b h.i k] using hw))
  by_cases hrc : r=c
  · subst r; exact Or.inl rfl
  by_cases hrj : r=h.j
  · rw [hrj]; exact Or.inr rfl
  by_cases hrd : r=d
  · subst r
    exact False.elim (selected_triple_forbidden p h.i k d (Ne.symm hki) hi.2.2.2 hh.2.2.2 hs
      (by simpa only [pair_comm d h.i] using h.side_pair h.i h.hi)
      (by simpa only [pair_comm d k] using h.side_pair k hkR) hw)
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  have hir : ({h.i,r}:Finset Coord)≠{h.i,h.j} := delta_pair_ne_right _ _ _ _ hri hrj
  exact False.elim (selected_triple_forbidden p h.i k r (Ne.symm hki) (Ne.symm hri) (Ne.symm hrk)
    hs (h.ordinary_corners h.i r h.hi hr (Ne.symm hri) hir).1
    (h.clean_corners k r hk hr (Ne.symm hrk)).1 hw)

theorem incident_middle_impossible (f : MissingAtNeighbor p a b) (k u v : Coord)
    (hk : k∈h.clean) (hu : u∈h.clean) (hv : v∈h.clean) (huv : u≠v)
    (hU : ∀s∈f.F,u∉s) (hV : ∀s∈f.F,v∉s)
    (hF : f.F={{h.i,h.j},{h.i,k}}) : False := by
  obtain ⟨hkR,hki,hkj⟩ := (h.mem_clean k).mp hk
  obtain ⟨huR,hui,huj⟩ := (h.mem_clean u).mp hu
  obtain ⟨hvR,hvi,hvj⟩ := (h.mem_clean v).mp hv
  have hi := (mem_distinctR a b c d h.i).mp h.hi
  have hj := (mem_distinctR a b c d h.j).mp h.hj
  have hh := (mem_distinctR a b c d k).mp hkR
  have hhu := (mem_distinctR a b c d u).mp huR
  have hhv := (mem_distinctR a b c d v).mp hvR
  have hikF : ({h.i,k}:Finset Coord)∈f.F := by rw [hF]; simp
  have hku : k≠u := by intro he; exact hU _ hikF (by simp [←he])
  have hkv : k≠v := by intro he; exact hV _ hikF (by simp [←he])
  have middle (x y : Coord) (hxy : x≠y) (hxa : x≠a) (hxb : x≠b) (hya : y≠a) (hyb : y≠b)
      (hx0 : ({x,y}:Finset Coord)≠{h.i,h.j}) (hx1 : ({x,y}:Finset Coord)≠{h.i,k}) :
      InPath p (triple a x y) := by
    apply (f.selected_iff x y hxy hxa hxb hya hyb).mpr
    rw [hF]; simpa only [mem_insert,mem_singleton,not_or] using And.intro hx0 hx1
  have hci := middle c h.i (Ne.symm hi.2.2.1) (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hi.1 hi.2.1
    (delta_pair_ne _ _ _ _ (Ne.symm hi.2.2.1) (Ne.symm hj.2.2.1))
    (delta_pair_ne _ _ _ _ (Ne.symm hi.2.2.1) (Ne.symm hh.2.2.1))
  have hck := middle c k (Ne.symm hh.2.2.1) (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hh.1 hh.2.1
    (delta_pair_ne _ _ _ _ (Ne.symm hi.2.2.1) (Ne.symm hj.2.2.1))
    (delta_pair_ne _ _ _ _ (Ne.symm hi.2.2.1) (Ne.symm hh.2.2.1))
  have hdk := middle d k (Ne.symm hh.2.2.2) (Ne.symm h.outer.had) (Ne.symm h.outer.hbd) hh.1 hh.2.1
    (delta_pair_ne _ _ _ _ (Ne.symm hi.2.2.2) (Ne.symm hj.2.2.2))
    (delta_pair_ne _ _ _ _ (Ne.symm hi.2.2.2) (Ne.symm hh.2.2.2))
  have hcd := middle c d h.outer.hcd (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc)
    (Ne.symm h.outer.had) (Ne.symm h.outer.hbd)
    (delta_pair_ne _ _ _ _ (Ne.symm hi.2.2.1) (Ne.symm hj.2.2.1))
    (delta_pair_ne _ _ _ _ (Ne.symm hi.2.2.1) (Ne.symm hh.2.2.1))
  have hp : InPath p (pair h.i k) := by
    simpa only [pair_comm k h.i] using (h.clean_corners k h.i hk h.hi hki).1
  have hnp := h.nonlow_outside_two f u v hu hv huv hU hV (pair h.i k) hp
    (by simp [bit_pair,Ne.symm hui,hku]) (by simp [bit_pair,Ne.symm hvi,hkv])
  have hcik := (force_two_neighbors p (pair h.i k) (triple h.i k c) (triple h.i k h.j)
    hnp (h.incident_pair_cover f k hk hikF)).1
  have hnrow := h.nonlow_outside_two f u v hu hv huv hU hV (pair b k) (h.row_selected k hkR)
    (by simp [bit_pair,Ne.symm hhu.2.1,hku]) (by simp [bit_pair,Ne.symm hhv.2.1,hkv])
  have hbkc := (force_two_neighbors p (pair b k) (triple b k c) (triple b k d) hnrow
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
  have cover : ∀w,InPath p w → Adj (triple a c k) w →
      w=quad a b c k ∨ w=quad a c k h.i := by
    intro w hw hadj
    obtain ⟨r,rfl⟩ := neighbor_triple a c k hadj
    by_cases hra : r=a
    · subst r; rw [quad_cancel_first] at hw; exact False.elim (hnck hw)
    by_cases hrc : r=c
    · subst r; rw [quad_cancel_second] at hw
      exact False.elim (h.absent_pair_a k hh.1 hh.2.1 hw)
    by_cases hrk : r=k
    · subst r; rw [quad_cancel_third] at hw
      exact False.elim (h.absent_pair_a c (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hw)
    by_cases hrb : r=b
    · subst r; left; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    by_cases hri : r=h.i
    · rw [hri]; exact Or.inr rfl
    by_cases hrd : r=d
    · subst r
      exact False.elim (ordinary_quad_absent p a c k d h.outer.hac hh.2.2.1 (Ne.symm h.outer.hcd)
        hh.2.2.2 hck hcd (by simpa only [triple_swap a d k] using hdk) hw)
    have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
    have ht := middle k r (Ne.symm hrk) hh.1 hh.2.1 hra hrb
      (delta_pair_ne k r h.i h.j hki hkj)
      (delta_pair_ne_right k r h.i k hri hrk)
    have hs := h.clean_corners k r hk hr (Ne.symm hrk)
    apply False.elim (two_layer_saturation p a b k r c h.outer.hab
      (Ne.symm h.outer.hac) (Ne.symm h.outer.hbc) hs.1 hs.2 ht _)
    have he : quad a c k r=quad a k r c := by apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    exact he ▸ hw
  have hntriple := h.nonlow_outside_two f u v hu hv huv hU hV (triple a c k) hck
    (by simp [bit_triple,Ne.symm hhu.1,Ne.symm hhu.2.2.1,hku])
    (by simp [bit_triple,Ne.symm hhv.1,Ne.symm hhv.2.2.1,hkv])
  have hq := (force_two_neighbors p (triple a c k) (quad a b c k) (quad a c k h.i) hntriple cover).2
  have hforbid := ordinary_quad_absent p c a k h.i (Ne.symm h.outer.hac) hh.1 hi.1 hki
    (by simpa only [triple,pair_comm c a] using hck)
    (by simpa only [triple,pair_comm c a] using hci)
    (by have he : triple h.i k c=triple c k h.i := by apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
        exact he ▸ hcik)
  apply hforbid
  simpa only [quad_swap_first a c k h.i] using hq

end EqualOuterPairConfig
#print axioms EqualOuterPairConfig.incident_middle_impossible
end
end Snake9
