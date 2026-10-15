import EqualOuterPairBase
import StarOuterResidual

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

namespace EqualOuterPairConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : EqualOuterPairConfig p a b c d)
include h

theorem isolated_endpoint (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈h.clean) (hisol : ∀s∈f.F,k∉s) :
    ∃w,InPath p w ∧ AtMostOneNeighbor p w ∧ DenseRowResource a b c d k w := by
  have hkR := (h.mem_clean k).mp hk |>.1
  have ht := h.toLocal.isolated_middle_selected f k hkR hk hisol
  rcases h.toLocal.isolated_endpoint_group f k hkR hk (h.row_selected k hkR) hisol with hl | hl | hl
  · exact ⟨pair b k,h.row_selected k hkR,hl,Or.inl rfl⟩
  · exact ⟨triple a c k,ht.1,hl,Or.inr (Or.inl rfl)⟩
  · exact ⟨triple a d k,ht.2,hl,Or.inr (Or.inr rfl)⟩

theorem resource_bit_self (k : Coord) (hk : k∈distinctR a b c d) (w : Vertex)
    (hw : DenseRowResource a b c d k w) : w.val.testBit k.val=true := by
  obtain ⟨hka,hkb,hkc,hkd⟩ := (mem_distinctR a b c d k).mp hk
  rcases hw with rfl | rfl | rfl <;>
    simp [bit_pair,bit_triple,Ne.symm hka,Ne.symm hkb,Ne.symm hkc,Ne.symm hkd]

theorem resource_bit_other (k r : Coord) (hr : r∈distinctR a b c d) (hkr : k≠r)
    (w : Vertex) (hw : DenseRowResource a b c d k w) : w.val.testBit r.val=false := by
  obtain ⟨hra,hrb,hrc,hrd⟩ := (mem_distinctR a b c d r).mp hr
  rcases hw with rfl | rfl | rfl <;>
    simp [bit_pair,bit_triple,Ne.symm hra,Ne.symm hrb,Ne.symm hrc,Ne.symm hrd,hkr]

theorem nonlow_outside_two (f : MissingAtNeighbor p a b) (u v : Coord)
    (hu : u∈h.clean) (hv : v∈h.clean) (huv : u≠v)
    (hU : ∀s∈f.F,u∉s) (hV : ∀s∈f.F,v∉s)
    (w : Vertex) (hw : InPath p w)
    (hwu : w.val.testBit u.val=false) (hwv : w.val.testBit v.val=false) : ¬AtMostOneNeighbor p w := by
  have huR := ((h.mem_clean u).mp hu).1
  have hvR := ((h.mem_clean v).mp hv).1
  obtain ⟨x,hx,hlx,hgx⟩ := h.isolated_endpoint f u hu hU
  obtain ⟨y,hy,hly,hgy⟩ := h.isolated_endpoint f v hv hV
  have hxy : x≠y := by
    intro he
    have hh := congrArg (fun z : Vertex => z.val.testBit u.val) he
    dsimp only at hh
    rw [h.resource_bit_self u huR x hgx,h.resource_bit_other v u huR (Ne.symm huv) y hgy] at hh
    contradiction
  have hxw : x≠w := by
    intro he
    have hh := congrArg (fun z : Vertex => z.val.testBit u.val) he
    dsimp only at hh
    rw [h.resource_bit_self u huR x hgx,hwu] at hh
    contradiction
  have hyw : y≠w := by
    intro he
    have hh := congrArg (fun z : Vertex => z.val.testBit v.val) he
    dsimp only at hh
    rw [h.resource_bit_self v hvR y hgy,hwv] at hh
    contradiction
  intro hlw
  exact (three_low_degree_vertices_repeat p hx hy hw hlx hly hlw).elim hxy (fun hh => hh.elim hxw hyw)

theorem clean_corners (x y : Coord) (hx : x∈h.clean)
    (hy : y∈distinctR a b c d) (hxy : x≠y) :
    InPath p (pair x y) ∧ InPath p (quad a b x y) :=
  h.toLocal.ordinary_corners x y hx ((h.mem_clean x).mp hx).1 hy hxy

theorem clean_b_absent (x y : Coord) (hx : x∈h.clean)
    (hy : y∈distinctR a b c d) (hxy : x≠y) : ¬InPath p (triple b x y) := by
  have hxR := ((h.mem_clean x).mp hx).1
  have hhx := (mem_distinctR a b c d x).mp hxR
  have hhy := (mem_distinctR a b c d y).mp hy
  have hs := h.clean_corners x y hx hy hxy
  exact middle_row_triple_forbidden p a b x y h.outer.hab (Ne.symm hhx.1)
    (Ne.symm hhy.1) (Ne.symm hhx.2.1) (Ne.symm hhy.2.1) hxy
    (h.row_selected x hxR) hs.1 hs.2

theorem missing_clean_pair_cover (f : MissingAtNeighbor p a b) (x y : Coord)
    (hx : x∈h.clean) (hy : y∈h.clean) (hxy : x≠y)
    (hm : ({x,y}:Finset Coord)∈f.F) :
    ∀w,InPath p w → Adj (pair x y) w → w=triple x y c ∨ w=triple x y d := by
  have hxR := ((h.mem_clean x).mp hx).1
  have hyR := ((h.mem_clean y).mp hy).1
  have hhx := (mem_distinctR a b c d x).mp hxR
  have hhy := (mem_distinctR a b c d y).mp hyR
  have hs := h.clean_corners x y hx hyR hxy
  have hna : ¬InPath p (triple a x y) := fun ht =>
    (f.selected_iff x y hxy hhx.1 hhx.2.1 hhy.1 hhy.2.1).mp ht hm
  intro w hw hadj
  obtain ⟨r,rfl⟩ := neighbor_pair x y hadj
  by_cases hrx : r=x
  · subst r; rw [triple_cancel_left] at hw
    exact False.elim (h.outer.absent_unit y hhy.1 hhy.2.2.1 hw)
  by_cases hry : r=y
  · subst r; rw [triple_cancel_right] at hw
    exact False.elim (h.outer.absent_unit x hhx.1 hhx.2.2.1 hw)
  by_cases hra : r=a
  · subst r; rw [triple_rotate] at hw; exact False.elim (hna hw)
  by_cases hrb : r=b
  · subst r; rw [triple_rotate] at hw; exact False.elim (h.clean_b_absent x y hx hyR hxy hw)
  by_cases hrc : r=c
  · subst r; exact Or.inl rfl
  by_cases hrd : r=d
  · subst r; exact Or.inr rfl
  have hr := (mem_distinctR a b c d r).mpr ⟨hra,hrb,hrc,hrd⟩
  exact False.elim (selected_triple_forbidden p x y r hxy (Ne.symm hrx) (Ne.symm hry)
    hs.1 (h.clean_corners x r hx hr (Ne.symm hrx)).1
    (h.clean_corners y r hy hr (Ne.symm hry)).1 hw)

theorem missing_clean_pair_low (f : MissingAtNeighbor p a b) (x y : Coord)
    (hx : x∈h.clean) (hy : y∈h.clean) (hxy : x≠y)
    (hm : ({x,y}:Finset Coord)∈f.F) : AtMostOneNeighbor p (pair x y) := by
  have hxR := ((h.mem_clean x).mp hx).1
  have hyR := ((h.mem_clean y).mp hy).1
  have hhx := (mem_distinctR a b c d x).mp hxR
  have hhy := (mem_distinctR a b c d y).mp hyR
  have unique (w : Vertex) (hw : InPath p w) (hadj : Adj (pair x y) w) : w=triple x y c := by
    rcases h.missing_clean_pair_cover f x y hx hy hxy hm w hw hadj with he | he
    · exact he
    · have hdx : InPath p (pair x d) := by simpa only [pair_comm d x] using h.side_pair x hxR
      have hdy : InPath p (pair y d) := by simpa only [pair_comm d y] using h.side_pair y hyR
      exact False.elim (selected_triple_forbidden p x y d hxy hhx.2.2.2 hhy.2.2.2
        (h.clean_corners x y hx hyR hxy).1 hdx hdy (he ▸ hw))
  intro w z hw hz haw haz
  exact (unique w hw haw).trans (unique z hz haz).symm

theorem mirror_clean (x : Coord) (hx : x∈h.clean) : x∈h.mirror.clean := by
  obtain ⟨hxR,hxi,hxj⟩ := (h.mem_clean x).mp hx
  have hh := (mem_distinctR a b c d x).mp hxR
  exact (h.mirror.mem_clean x).mpr
    ⟨(mem_distinctR b a d c x).mpr ⟨hh.2.1,hh.1,hh.2.2.2,hh.2.2.1⟩,hxi,hxj⟩

theorem missing_clean_quad_low (f : MissingAtNeighbor p a b) (x y : Coord)
    (hx : x∈h.clean) (hy : y∈h.clean) (hxy : x≠y)
    (hm : ({x,y}:Finset Coord)∈f.F) : AtMostOneNeighbor p (quad a b x y) := by
  have hl := h.mirror.missing_clean_pair_low f.mirror x y (h.mirror_clean x hx)
    (h.mirror_clean y hy) hxy hm
  have ht := low_of_translate p (pair a b) (pair x y) hl
  simpa only [quad,triple,pair,vxor_assoc] using ht

end EqualOuterPairConfig
#print axioms EqualOuterPairConfig.nonlow_outside_two
#print axioms EqualOuterPairConfig.missing_clean_quad_low
end
end Snake9
