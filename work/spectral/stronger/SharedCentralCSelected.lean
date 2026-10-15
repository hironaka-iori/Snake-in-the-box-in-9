import SharedCentralDouble

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 2500000
namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem ordinary_pair_internal (f : MissingAtNeighbor p a b)
    (hF : ∀S∈f.F,S⊆{c,d,h.e,h.x,h.y}) (i j : Coord)
    (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d)
    (hp : InPath p (pair i j)) : ¬AtMostOneNeighbor p (pair i j) := by
  obtain ⟨u,v,huv,hu,hue,hux,huy,hv,hve,hvx,hvy⟩ := h.two_clean_indices
  have good (k : Coord) (hk : k∈distinctR a b c d) (hke : k≠h.e) (hkx : k≠h.x) (hky : k≠h.y) :
      OrdinaryGoodRow f.F (distinctR a b c d) h.ordinary.A h.ordinary.B c d k := by
    apply h.clean_isolated_good f k hk hke hkx hky
    intro s hs hks
    have hh := (mem_distinctR a b c d k).mp hk
    have hb := hF s hs hks
    simpa [hh.2.2.1,hh.2.2.2,hke,hkx,hky] using hb
  obtain ⟨z,hz,hlz,hgz⟩ := h.ordinary.good_row_endpoint f u hu (good u hu hue hux huy)
  obtain ⟨w,hw,hlw,hgw⟩ := h.ordinary.good_row_endpoint f v hv (good v hv hve hvx hvy)
  have hzw := active_endpoint_groups_disjoint a b c d u v hu huv z w hgz hgw
  have distinct (k : Coord) (hk : k∈distinctR a b c d) (q : Vertex)
      (hq : ActiveEndpointMember a b c d k q) : q≠pair i j := by
    have hh := (mem_distinctR a b c d k).mp hk
    have hi' := (mem_distinctR a b c d i).mp hi
    have hj' := (mem_distinctR a b c d j).mp hj
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals intro he
    · have hb := congrArg (fun q : Vertex => q.val.testBit b.val) he
      simp [bit_pair,hh.2.1,hi'.2.1,hj'.2.1] at hb
    · have hb := congrArg (fun q : Vertex => q.val.testBit a.val) he
      simp [bit_pair,bit_triple,Ne.symm h.ordinary.outer.hac,hh.1,hi'.1,hj'.1] at hb
    · have hb := congrArg (fun q : Vertex => q.val.testBit a.val) he
      simp [bit_pair,bit_triple,Ne.symm h.ordinary.outer.had,hh.1,hi'.1,hj'.1] at hb
    · have hb := congrArg (fun q : Vertex => q.val.testBit d.val) he
      simp [bit_pair,hh.2.2.2,hi'.2.2.2,hj'.2.2.2] at hb
    · have hb := congrArg (fun q : Vertex => q.val.testBit a.val) he
      simp [bit_pair,bit_quad,Ne.symm h.ordinary.outer.hab,Ne.symm h.ordinary.outer.hac,hh.1,hi'.1,hj'.1] at hb
  intro hl
  rcases three_low_degree_vertices_repeat p hz hw hp hlz hlw hl with he | he | he
  · exact hzw he
  · exact distinct u hu z hgz he
  · exact distinct v hv w hgw he

theorem ordinary_clean_pair_cover (i j : Coord)
    (hi : i∈distinctR a b c d) (hj : j∈distinctR a b c d) (hij : i≠j)
    (hiA : i∉h.ordinary.A) (hjA : j∉h.ordinary.A) :
    ∀w,InPath p w → Adj (pair i j) w → w=triple i j a ∨ w=triple i j c := by
  have hhi := (mem_distinctR a b c d i).mp hi
  have hhj := (mem_distinctR a b c d j).mp hj
  have hs := h.ordinary.left_clean_pair i j hi hj hij hiA
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_pair i j hadj
  by_cases hri : r=i
  · subst r; rw [triple_cancel_left] at hw
    exact False.elim (h.ordinary.outer.absent_unit j hhj.1 hhj.2.2.1 hw)
  by_cases hrj : r=j
  · subst r; rw [triple_cancel_right] at hw
    exact False.elim (h.ordinary.outer.absent_unit i hhi.1 hhi.2.2.1 hw)
  by_cases hra : r=a
  · subst r; exact Or.inl rfl
  by_cases hrc : r=c
  · subst r; exact Or.inr rfl
  by_cases hrb : r=b
  · subst r; rw [triple_rotate] at hw
    exact False.elim (h.ordinary.ordinary_b_absent i j hi hj hij hw)
  by_cases hrd : r=d
  · subst r
    exact False.elim (selected_triple_forbidden p i j d hij hhi.2.2.2 hhj.2.2.2 hs
      (by simpa only [pair_comm d i] using h.ordinary.side_pair i hi)
      (by simpa only [pair_comm d j] using h.ordinary.side_pair j hj) hw)
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  exact False.elim (selected_triple_forbidden p i j r hij (Ne.symm hri) (Ne.symm hrj) hs
    (h.ordinary.left_clean_pair i r hi hr (Ne.symm hri) hiA)
    (h.ordinary.left_clean_pair j r hj hr (Ne.symm hrj) hjA) hw)

theorem ce_de_c_row_absent (f : MissingAtNeighbor p a b) (hF : f.F={{c,h.e},{d,h.e}})
    (r : Coord) (hr : r∈distinctR a b c d) : ¬InPath p (pair c r) := by
  have hh := (mem_distinctR a b c d r).mp hr
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hy := (mem_distinctR a b c d h.y).mp h.hy
  have core_row (k : Coord) (hk : k∈distinctR a b c d) (hkcore : k=h.e ∨ k=h.x ∨ k=h.y) :
      InPath p (triple b k c) := by
    apply (force_two_neighbors p (pair b k) (triple b k c) (triple b k d)
      ?_ (h.ordinary.row_cover k hk)).1
    apply h.core_internal f (h.ce_de_support f hF) _ (h.ordinary.row_selected k hk)
    intro z hz hze hzx hzy
    have hz' := (mem_distinctR a b c d z).mp hz
    rcases hkcore with rfl | rfl | rfl <;>
      simp [bit_pair,Ne.symm hz'.2.1,Ne.symm hze,Ne.symm hzx,Ne.symm hzy]
  by_cases hre : r=h.e
  · subst r
    have ht := core_row h.e h.he (Or.inl rfl)
    have hq := h.ordinary.side_quad h.e h.he
    intro hp
    apply selected_flip_forbidden p (triple b h.e c) c a b
      (Ne.symm h.ordinary.outer.hac) (Ne.symm h.ordinary.outer.hbc) h.ordinary.outer.hab ht
    · change InPath p (quad b h.e c c)
      rw [quad_cancel_third]; exact h.ordinary.row_selected h.e h.he
    · have heq : SquareIncidence.flip a (triple b h.e c)=quad a b c h.e := by
        apply Fin.ext; dsimp [SquareIncidence.flip,quad,triple,pair,vxor]; ac_rfl
      exact heq.symm ▸ hq
    · change InPath p (quad b h.e c b)
      rw [quad_cancel_first,pair_comm]; exact hp
  have hacr := h.ce_de_middle_without_e f hF c r (Ne.symm hh.2.2.1)
    (Ne.symm h.ordinary.outer.hac) (Ne.symm h.ordinary.outer.hbc) (Ne.symm he.2.2.1)
    hh.1 hh.2.1 hre
  have forbid (s : Coord) (hsa : s≠a) (hsr : s≠r)
      (ht : InPath p (triple c r s)) : ¬InPath p (pair c r) := by
    intro hp
    apply selected_flip_forbidden p (pair c r) r a s hh.1 (Ne.symm hsr) (Ne.symm hsa) hp
    · change InPath p (triple c r r); rw [triple_cancel_right]; exact h.ordinary.outer.hc
    · change InPath p (triple c r a); rw [triple_rotate]; exact hacr
    · exact ht
  by_cases hrx : r=h.x
  · apply forbid b (Ne.symm h.ordinary.outer.hab) (Ne.symm hh.2.1)
    have ht := core_row r hr (Or.inr (Or.inl hrx))
    have heq : triple b r c=triple c r b := by apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
    exact heq ▸ ht
  by_cases hry : r=h.y
  · apply forbid b (Ne.symm h.ordinary.outer.hab) (Ne.symm hh.2.1)
    have ht := core_row r hr (Or.inr (Or.inr hry))
    have heq : triple b r c=triple c r b := by apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
    exact heq ▸ ht
  have hyA : h.y∉h.ordinary.A := by simp [h.Aeq,Ne.symm h.hey,Ne.symm h.hxy]
  have hrA : r∉h.ordinary.A := by simp [h.Aeq,hre,hrx]
  have hp := h.ordinary.left_clean_pair h.y r h.hy hr (Ne.symm hry) hyA
  have hn := h.ordinary_pair_internal f (h.ce_de_support f hF) h.y r h.hy hr hp
  have ht := (force_two_neighbors p (pair h.y r) (triple h.y r a) (triple h.y r c)
    hn (h.ordinary_clean_pair_cover h.y r h.hy hr (Ne.symm hry) hyA hrA)).2
  apply forbid h.y hy.1 (Ne.symm hry)
  have heq : triple h.y r c=triple c r h.y := by apply Fin.ext; dsimp [triple,pair,vxor]; ac_rfl
  exact heq ▸ ht

theorem central_c_pair_selected (f : MissingAtNeighbor p a b)
    (hF : f.F={{c,h.e},{d,h.e}}) : InPath p (pair c d) := by
  have hn : ¬AtMostOneNeighbor p (unit c) := by
    apply h.core_internal f (h.ce_de_support f hF) _ h.ordinary.outer.hc
    intro k hk hke hkx hky
    have hh := (mem_distinctR a b c d k).mp hk
    simp [bit_unit,Ne.symm hh.2.2.1]
  apply (force_two_neighbors p (unit c) 0 (pair c d) hn ?_).2
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_unit c hadj
  by_cases hrc : r=c
  · subst r; exact Or.inl (pair_self _)
  by_cases hrd : r=d
  · subst r; exact Or.inr rfl
  by_cases hra : r=a
  · subst r; rw [pair_comm] at hw
    exact False.elim (h.ordinary.absent_pair_a c (Ne.symm h.ordinary.outer.hac) (Ne.symm h.ordinary.outer.hbc) hw)
  by_cases hrb : r=b
  · subst r
    have hq : InPath p (quad a b a c) := by rw [quad_swap_last,quad_cancel_first,pair_comm]; exact hw
    have hm := (h.ordinary.outer.right_pair_iff a c h.ordinary.outer.hac h.ordinary.outer.hab
      h.ordinary.outer.had (Ne.symm h.ordinary.outer.hbc) h.ordinary.outer.hcd).mp hq
    rw [h.ordinary.right_eq] at hm
    exact False.elim (hm (by simp))
  exact False.elim (h.ce_de_c_row_absent f hF r ((mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩) hw)

end SharedOuterConfig
#print axioms SharedOuterConfig.central_c_pair_selected
end
end Snake9

