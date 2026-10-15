import SharedOuterBase
import StarOuterResidual

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 2200000
set_option maxRecDepth 100000

namespace SharedOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : SharedOuterConfig p a b c d)
include h

theorem cross_pair_selected : InPath p (pair h.x h.y) := by
  apply (h.ordinary.left_pair_iff h.x h.y h.hx h.hy h.hxy).mpr
  rw [h.Aeq]
  exact delta_pair_ne_right _ _ _ _ (Ne.symm h.hey) (Ne.symm h.hxy)

theorem cross_quad_selected : InPath p (quad a b h.x h.y) := by
  apply (h.ordinary.right_pair_iff h.x h.y h.hx h.hy h.hxy).mpr
  rw [h.Beq]
  exact delta_pair_ne _ _ _ _ (Ne.symm h.hex) h.hxy

theorem cross_pair_cover (f : MissingAtNeighbor p a b) (hm : ({h.x,h.y}:Finset Coord)∈f.F) :
    ∀w,InPath p w → Adj (pair h.x h.y) w →
      w=triple h.x h.y c ∨ w=triple h.x h.y h.e := by
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have hy := (mem_distinctR a b c d h.y).mp h.hy
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_pair h.x h.y hadj
  by_cases hrx : r=h.x
  · rw [hrx,triple_cancel_left] at hw
    exact False.elim (h.ordinary.outer.absent_unit h.y hy.1 hy.2.2.1 hw)
  by_cases hry : r=h.y
  · rw [hry,triple_cancel_right] at hw
    exact False.elim (h.ordinary.outer.absent_unit h.x hx.1 hx.2.2.1 hw)
  by_cases hra : r=a
  · subst r; rw [triple_rotate] at hw
    exact False.elim ((f.selected_iff h.x h.y h.hxy hx.1 hx.2.1 hy.1 hy.2.1).mp hw hm)
  by_cases hrb : r=b
  · subst r; rw [triple_rotate] at hw
    exact False.elim (h.ordinary.ordinary_b_absent h.x h.y h.hx h.hy h.hxy hw)
  by_cases hrc : r=c
  · subst r; exact Or.inl rfl
  by_cases hre : r=h.e
  · rw [hre]; exact Or.inr rfl
  by_cases hrd : r=d
  · subst r
    exact False.elim (selected_triple_forbidden p h.x h.y d h.hxy hx.2.2.2 hy.2.2.2 h.cross_pair_selected
      (by simpa only [pair_comm d h.x] using h.ordinary.side_pair h.x h.hx)
      (by simpa only [pair_comm d h.y] using h.ordinary.side_pair h.y h.hy) hw)
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  have hxr : InPath p (pair h.x r) := by
    apply (h.ordinary.left_pair_iff h.x r h.hx hr (Ne.symm hrx)).mpr
    rw [h.Aeq]; exact delta_pair_ne_right _ _ _ _ hre hrx
  have hyr : InPath p (pair h.y r) := by
    apply (h.ordinary.left_pair_iff h.y r h.hy hr (Ne.symm hry)).mpr
    rw [h.Aeq]; exact delta_pair_ne _ _ _ _ (Ne.symm h.hey) (Ne.symm h.hxy)
  exact False.elim (selected_triple_forbidden p h.x h.y r h.hxy (Ne.symm hrx) (Ne.symm hry)
    h.cross_pair_selected hxr hyr hw)

theorem switch_hole_selected (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hke : k≠h.e) (hkx : k≠h.x) (hky : k≠h.y)
    (hF : f.F={{h.e,k},{h.x,h.y}}) : InPath p (triple a h.e h.x) := by
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  apply (f.selected_iff h.e h.x h.hex he.1 he.2.1 hx.1 hx.2.1).mpr
  rw [hF]; simp only [mem_insert,mem_singleton,not_or]
  exact ⟨delta_pair_ne_right _ _ _ _ (Ne.symm h.hex) (Ne.symm hkx),delta_pair_ne _ _ _ _ h.hex h.hey⟩

theorem switch_left_hole_cover (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hke : k≠h.e) (hkx : k≠h.x) (hky : k≠h.y)
    (hF : f.F={{h.e,k},{h.x,h.y}}) :
    ∀w,InPath p w → Adj (triple a h.e h.x) w →
      w=quad a b h.e h.x ∨ w=quad a h.e h.x h.y := by
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have hy := (mem_distinctR a b c d h.y).mp h.hy
  have hhk := (mem_distinctR a b c d k).mp hk
  have ht := h.switch_hole_selected f k hk hke hkx hky hF
  have hspecial (s : Coord) (hsa : s≠a) (hsb : s≠b)
      (hse : s≠h.e) (hsx : s≠h.x) (hsy : s≠h.y) (hsk : s≠k) :
      ¬InPath p (quad a h.e h.x s) := by
    have star (t : Coord) (hst : s≠t) (hta : t≠a) (htb : t≠b) : InPath p (triple a s t) := by
      apply (f.selected_iff s t hst hsa hsb hta htb).mpr
      rw [hF]; simp only [mem_insert,mem_singleton,not_or]
      exact ⟨delta_pair_ne _ _ _ _ hse hsk,delta_pair_ne _ _ _ _ hsx hsy⟩
    exact ordinary_quad_absent p a h.e h.x s (Ne.symm he.1) (Ne.symm h.hex) hse (Ne.symm hsx)
      ht (by simpa only [triple_swap a s h.e] using star h.e hse he.1 he.2.1)
      (by simpa only [triple_swap a s h.x] using star h.x hsx hx.1 hx.2.1)
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_triple a h.e h.x hadj
  by_cases hra : r=a
  · subst r; rw [quad_cancel_first] at hw
    exact False.elim ((h.ordinary.left_pair_iff h.e h.x h.he h.hx h.hex).mp hw h.Aeq.symm)
  by_cases hre : r=h.e
  · rw [hre,quad_cancel_second] at hw
    exact False.elim (h.ordinary.absent_pair_a h.x hx.1 hx.2.1 hw)
  by_cases hrx : r=h.x
  · rw [hrx,quad_cancel_third] at hw
    exact False.elim (h.ordinary.absent_pair_a h.e he.1 he.2.1 hw)
  by_cases hrb : r=b
  · subst r; left; apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
  by_cases hrc : r=c
  · subst r
    exact False.elim (hspecial c (Ne.symm h.ordinary.outer.hac) (Ne.symm h.ordinary.outer.hbc)
      (Ne.symm he.2.2.1) (Ne.symm hx.2.2.1) (Ne.symm hy.2.2.1) (Ne.symm hhk.2.2.1) hw)
  by_cases hrd : r=d
  · subst r
    exact False.elim (hspecial d (Ne.symm h.ordinary.outer.had) (Ne.symm h.ordinary.outer.hbd)
      (Ne.symm he.2.2.2) (Ne.symm hx.2.2.2) (Ne.symm hy.2.2.2) (Ne.symm hhk.2.2.2) hw)
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  have hres := (h.ordinary.left_hole_extension f h.e h.x r h.hex h.Aeq.symm hr hre hrx hw).2
  have hry : r=h.y := by
    rcases hres with hm | hb
    · rw [hF] at hm
      rcases Finset.mem_insert.mp hm with hh | hh
      · exact False.elim (delta_pair_ne h.x r h.e k (Ne.symm h.hex) (Ne.symm hkx) hh)
      · have heq := Finset.mem_singleton.mp hh
        have hm : r∈({h.x,h.y}:Finset Coord) := heq ▸ (by simp : r∈({h.x,r}:Finset Coord))
        exact Finset.mem_singleton.mp ((Finset.mem_insert.mp hm).resolve_left hrx)
    · rw [h.Beq] at hb
      exact False.elim (delta_pair_ne h.x r h.e h.y (Ne.symm h.hex) h.hxy hb)
  rw [hry]
  exact Or.inr rfl

theorem switch_both_holes_selected (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hke : k≠h.e) (hkx : k≠h.x) (hky : k≠h.y)
    (hF : f.F={{h.e,k},{h.x,h.y}}) :
    InPath p (triple a h.e h.x) ∧ InPath p (triple a h.e h.y) := by
  refine ⟨h.switch_hole_selected f k hk hke hkx hky hF,?_⟩
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hy := (mem_distinctR a b c d h.y).mp h.hy
  apply (f.selected_iff h.e h.y h.hey he.1 he.2.1 hy.1 hy.2.1).mpr
  rw [hF]; simp only [mem_insert,mem_singleton,not_or]
  exact ⟨delta_pair_ne_right _ _ _ _ (Ne.symm h.hey) (Ne.symm hky),delta_pair_ne _ _ _ _ h.hex h.hey⟩

theorem switch_hole_low_of_absent (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hke : k≠h.e) (hkx : k≠h.x) (hky : k≠h.y)
    (hF : f.F={{h.e,k},{h.x,h.y}}) (hnq : ¬InPath p (quad a h.e h.x h.y)) :
    AtMostOneNeighbor p (triple a h.e h.x) := by
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (triple a h.e h.x) w) : w=quad a b h.e h.x := by
    rcases h.switch_left_hole_cover f k hk hke hkx hky hF w hw hadj with he | he
    · exact he
    · exact False.elim (hnq (he ▸ hw))
  intro x y hx hy hax hay
  exact (unique x hx hax).trans (unique y hy hay).symm

theorem switch_pair_low_of_present (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hke : k≠h.e) (hkx : k≠h.x) (hky : k≠h.y)
    (hF : f.F={{h.e,k},{h.x,h.y}}) (hq : InPath p (quad a h.e h.x h.y)) :
    AtMostOneNeighbor p (pair h.x h.y) := by
  have he := (mem_distinctR a b c d h.e).mp h.he
  have hx := (mem_distinctR a b c d h.x).mp h.hx
  have hy := (mem_distinctR a b c d h.y).mp h.hy
  have hs := h.switch_both_holes_selected f k hk hke hkx hky hF
  have hn := quad_two_rows_excludes_side p a h.e h.x h.y (Ne.symm he.1) (Ne.symm hx.1)
    (Ne.symm hy.1) h.hxy hq hs.1 hs.2
  have hm : ({h.x,h.y}:Finset Coord)∈f.F := by rw [hF]; simp
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (pair h.x h.y) w) : w=triple h.x h.y c := by
    rcases h.cross_pair_cover f hm w hw hadj with he | he
    · exact he
    · have ht : InPath p (triple h.x h.y h.e) := he ▸ hw
      exact False.elim (hn (by simpa only [triple_rotate h.x h.y h.e] using ht))
  intro x y hx hy hax hay
  exact (unique x hx hax).trans (unique y hy hay).symm

theorem switch_two_endpoints (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hke : k≠h.e) (hkx : k≠h.x) (hky : k≠h.y)
    (hF : f.F={{h.e,k},{h.x,h.y}}) :
    (AtMostOneNeighbor p (triple a h.e h.x) ∧ AtMostOneNeighbor p (triple a h.e h.y)) ∨
    (AtMostOneNeighbor p (pair h.x h.y) ∧ AtMostOneNeighbor p (quad a b h.x h.y)) := by
  have hh := (mem_distinctR a b c d k).mp hk
  have hkm := (mem_distinctR b a d c k).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩
  have hFm : f.mirror.F={{h.mirror.e,k},{h.mirror.x,h.mirror.y}} := by
    simpa only [mirror,Finset.pair_comm h.y h.x] using hF
  have heq : vxor (pair a b) (quad b h.e h.y h.x)=quad a h.e h.x h.y := by
    rw [quad_swap_last b h.e h.y h.x]
    simp only [quad,triple,pair,vxor_assoc,vxor_cancel]
  by_cases hq : InPath p (quad a h.e h.x h.y)
  · right
    refine ⟨h.switch_pair_low_of_present f k hk hke hkx hky hF hq,?_⟩
    have hqm : InPath (translate p (pair a b)) (quad b h.e h.y h.x) :=
      (inPath_translate_at p _ _).mpr (heq.symm ▸ hq)
    have hl := h.mirror.switch_pair_low_of_present f.mirror k hkm hke hky hkx hFm hqm
    have hl' := low_of_translate p (pair a b) (pair h.y h.x) hl
    simpa only [quad,triple,pair,vxor_assoc,vxor_comm (unit h.y) (unit h.x)] using hl'
  · left
    refine ⟨h.switch_hole_low_of_absent f k hk hke hkx hky hF hq,?_⟩
    have hnqm : ¬InPath (translate p (pair a b)) (quad b h.e h.y h.x) := by
      intro hs
      exact hq (heq ▸ (inPath_translate_at p _ _).mp hs)
    have hl := h.mirror.switch_hole_low_of_absent f.mirror k hkm hke hky hkx hFm hnqm
    have hl' := low_of_translate p (pair a b) (triple b h.e h.y) hl
    simpa only [triple,pair,vxor_assoc,vxor_cancel] using hl'

theorem switch_impossible (f : MissingAtNeighbor p a b) (k u : Coord)
    (hk : k∈distinctR a b c d) (hu : u∈distinctR a b c d)
    (hke : k≠h.e) (hkx : k≠h.x) (hky : k≠h.y)
    (hue : u≠h.e) (hux : u≠h.x) (huy : u≠h.y) (huk : u≠k)
    (hF : f.F={{h.e,k},{h.x,h.y}}) : False := by
  have hh := (mem_distinctR a b c d u).mp hu
  have hnuA : u∉h.ordinary.A := by simpa only [h.Aeq,mem_insert,mem_singleton,not_or] using And.intro hue hux
  have hnuB : u∉h.ordinary.B := by simpa only [h.Beq,mem_insert,mem_singleton,not_or] using And.intro hue huy
  let localRows : LocalDenseRows p a b c d := {
    outer := h.ordinary.outer
    rows := {u}
    ordinary_corners := by
      intro i j hi hiR hjR hij
      have hiu : i=u := Finset.mem_singleton.mp hi
      subst i
      constructor
      · apply (h.ordinary.left_pair_iff u j hu hjR hij).mpr
        intro he; exact hnuA (he ▸ (by simp : u∈({u,j}:Finset Coord)))
      · apply (h.ordinary.right_pair_iff u j hu hjR hij).mpr
        intro he; exact hnuB (he ▸ (by simp : u∈({u,j}:Finset Coord))) }
  have hisol : ∀s∈f.F,u∉s := by
    intro s hs
    rw [hF] at hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simpa only [mem_insert,mem_singleton,not_or] using And.intro hue huk
    · rw [Finset.mem_singleton.mp hs]
      simpa only [mem_insert,mem_singleton,not_or] using And.intro hux huy
  have hts := localRows.isolated_middle_selected f u hu (by simp [localRows]) hisol
  have hex : ∃w,InPath p w ∧ AtMostOneNeighbor p w ∧ w.val.testBit u.val=true := by
    rcases localRows.isolated_endpoint_group f u hu (by simp [localRows]) (h.ordinary.row_selected u hu) hisol with hl | hl | hl
    · exact ⟨pair b u,h.ordinary.row_selected u hu,hl,by simp [bit_pair,Ne.symm hh.2.1]⟩
    · exact ⟨triple a c u,hts.1,hl,by simp [bit_triple,Ne.symm hh.1,Ne.symm hh.2.2.1]⟩
    · exact ⟨triple a d u,hts.2,hl,by simp [bit_triple,Ne.symm hh.1,Ne.symm hh.2.2.2]⟩
  obtain ⟨w,hw,hlw,hbit⟩ := hex
  have close (x y : Vertex) (hx : InPath p x) (hy : InPath p y)
      (hlx : AtMostOneNeighbor p x) (hly : AtMostOneNeighbor p y) (hxy : x≠y)
      (hbx : x.val.testBit u.val=false) (hby : y.val.testBit u.val=false) : False := by
    have hn (z : Vertex) (hz : z.val.testBit u.val=false) : z≠w := by
      intro he
      have hb := congrArg (fun v : Vertex => v.val.testBit u.val) he
      dsimp only at hb
      rw [hz,hbit] at hb
      contradiction
    rcases three_low_degree_vertices_repeat p hx hy hw hlx hly hlw with he | he | he
    · exact hxy he
    · exact hn x hbx he
    · exact hn y hby he
  have hs := h.switch_both_holes_selected f k hk hke hkx hky hF
  rcases h.switch_two_endpoints f k hk hke hkx hky hF with hl | hl
  · apply close _ _ hs.1 hs.2 hl.1 hl.2
    · intro he; exact h.hxy (triple_injective_right a h.e h.x h.y he)
    · simp [bit_triple,Ne.symm hh.1,Ne.symm hue,Ne.symm hux]
    · simp [bit_triple,Ne.symm hh.1,Ne.symm hue,Ne.symm huy]
  · apply close _ _ h.cross_pair_selected h.cross_quad_selected hl.1 hl.2
    · intro he
      have hx := (mem_distinctR a b c d h.x).mp h.hx
      have hy := (mem_distinctR a b c d h.y).mp h.hy
      have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
      simp [bit_pair,bit_quad,Ne.symm h.ordinary.outer.hab,hx.1,hy.1] at hb
    · simp [bit_pair,Ne.symm hux,Ne.symm huy]
    · simp [bit_quad,Ne.symm hh.1,Ne.symm hh.2.1,Ne.symm hux,Ne.symm huy]

end SharedOuterConfig
#print axioms SharedOuterConfig.cross_pair_cover
#print axioms SharedOuterConfig.switch_left_hole_cover
#print axioms SharedOuterConfig.switch_impossible
end
end Snake9
