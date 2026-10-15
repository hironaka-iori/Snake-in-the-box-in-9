import StarOuterBase

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

def DenseRowResource (a b c d k : Coord) (w : Vertex) : Prop :=
  w=pair b k ∨ w=triple a c k ∨ w=triple a d k

namespace StarOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : StarOuterConfig p a b c d)
include h

theorem isolated_endpoint (f : MissingAtNeighbor p a b) (k : Coord)
    (hk : k∈distinctR a b c d) (hisol : ∀s∈f.F,k∉s) :
    ∃w,InPath p w ∧ AtMostOneNeighbor p w ∧ DenseRowResource a b c d k w := by
  have ht := h.toDense.isolated_middle_selected f k hk hisol
  rcases h.toDense.isolated_endpoint_group f k hk (h.row_selected k hk) hisol with hl | hl | hl
  · exact ⟨pair b k,h.row_selected k hk,hl,Or.inl rfl⟩
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
    (hu : u∈distinctR a b c d) (hv : v∈distinctR a b c d) (huv : u≠v)
    (hU : ∀s∈f.F,u∉s) (hV : ∀s∈f.F,v∉s)
    (w : Vertex) (hw : InPath p w)
    (hwu : w.val.testBit u.val=false) (hwv : w.val.testBit v.val=false) : ¬AtMostOneNeighbor p w := by
  obtain ⟨x,hx,hlx,hgx⟩ := h.isolated_endpoint f u hu hU
  obtain ⟨y,hy,hly,hgy⟩ := h.isolated_endpoint f v hv hV
  have hxy : x≠y := by
    intro he
    have hh := congrArg (fun z : Vertex => z.val.testBit u.val) he
    dsimp only at hh
    rw [h.resource_bit_self u hu x hgx,h.resource_bit_other v u hu (Ne.symm huv) y hgy] at hh
    contradiction
  have hxw : x≠w := by
    intro he
    have hh := congrArg (fun z : Vertex => z.val.testBit u.val) he
    dsimp only at hh
    rw [h.resource_bit_self u hu x hgx,hwu] at hh
    contradiction
  have hyw : y≠w := by
    intro he
    have hh := congrArg (fun z : Vertex => z.val.testBit v.val) he
    dsimp only at hh
    rw [h.resource_bit_self v hv y hgy,hwv] at hh
    contradiction
  intro hlw
  exact (three_low_degree_vertices_repeat p hx hy hw hlx hly hlw).elim hxy (fun hh => hh.elim hxw hyw)

theorem residual_impossible (f : MissingAtNeighbor p a b) (u v y : Coord)
    (hu : u∈distinctR a b c d) (hv : v∈distinctR a b c d) (huv : u≠v)
    (hU : ∀s∈f.F,u∉s) (hV : ∀s∈f.F,v∉s)
    (hy : y∈distinctR a b c d) (hyf : y≠h.f)
    (hfy : ({h.f,y}:Finset Coord)∈f.F) (hncy : ({c,y}:Finset Coord)∉f.F) : False := by
  have hhf := (mem_distinctR a b c d h.f).mp h.hf
  have hhy := (mem_distinctR a b c d y).mp hy
  have hhu := (mem_distinctR a b c d u).mp hu
  have hhv := (mem_distinctR a b c d v).mp hv
  have hfu : h.f≠u := by intro he; exact hU _ hfy (by simp [←he])
  have hfv : h.f≠v := by intro he; exact hV _ hfy (by simp [←he])
  have hyu : y≠u := by intro he; exact hU _ hfy (by simp [←he])
  have hyv : y≠v := by intro he; exact hV _ hfy (by simp [←he])
  have hnrow := h.nonlow_outside_two f u v hu hv huv hU hV (pair b y) (h.row_selected y hy)
    (by simp [bit_pair,Ne.symm hhu.2.1,hyu]) (by simp [bit_pair,Ne.symm hhv.2.1,hyv])
  have hbcy0 := (force_two_neighbors p (pair b y) (triple b y c) (triple b y d)
    hnrow (h.toDense.row_cover y hy (h.row_selected y hy))).1
  have hbcy : InPath p (triple b c y) := by simpa only [triple_swap b y c] using hbcy0
  have hacy := (f.selected_iff c y (Ne.symm hhy.2.2.1) (Ne.symm h.outer.hac)
    (Ne.symm h.outer.hbc) hhy.1 hhy.2.1).mpr hncy
  have hqab := (h.ordinary_corners h.f y h.hf hy (Ne.symm hyf)).2
  have hnquad := h.nonlow_outside_two f u v hu hv huv hU hV (quad a b h.f y) hqab
    (by simp [bit_quad,Ne.symm hhu.1,Ne.symm hhu.2.1,hfu,hyu])
    (by simp [bit_quad,Ne.symm hhv.1,Ne.symm hhv.2.1,hfv,hyv])
  have hfm : h.f∈distinctR b a d c := (mem_distinctR b a d c h.f).mpr
    ⟨hhf.2.1,hhf.1,hhf.2.2.2,hhf.2.2.1⟩
  have hym : y∈distinctR b a d c := (mem_distinctR b a d c y).mpr
    ⟨hhy.2.1,hhy.1,hhy.2.2.2,hhy.2.2.1⟩
  have hntrans : ¬AtMostOneNeighbor (translate p (pair a b)) (pair h.f y) := by
    intro hl
    have ht := low_of_translate p (pair a b) (pair h.f y) hl
    exact hnquad (by simpa only [quad,triple,pair,vxor_assoc] using ht)
  have htq := (force_two_neighbors (translate p (pair a b)) (pair h.f y)
    (triple h.f y d) (triple h.f y c) hntrans
    (h.mirror.missing_pair_cover f.mirror h.f y hfm hym (Ne.symm hyf) hfy)).2
  have hbig : InPath p (vxor (pair a b) (triple h.f y c)) := (inPath_translate_at p _ _).mp htq
  have hside := h.side_quad y hy hyf
  have adj1 : Adj (quad a b c y) (triple a c y) := by
    have he : quad a b c y=quad a c y b := by apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    rw [he]; exact adj_symmetric (triple_quad_adj _ _ _ _)
  have adj2 : Adj (quad a b c y) (triple b c y) := by
    rw [←quad_rotate b c y a]; exact adj_symmetric (triple_quad_adj _ _ _ _)
  have adj3 : Adj (quad a b c y) (vxor (pair a b) (triple h.f y c)) := by
    have he : vxor (pair a b) (triple h.f y c)=vxor (quad a b c y) (unit h.f) := by
      apply Fin.ext; dsimp [quad,triple,pair,vxor]; ac_rfl
    rw [he]; exact adj_flip _ _
  have bigbit : (vxor (pair a b) (triple h.f y c)).val.testBit h.f.val=true := by
    change ((pair a b).val ^^^ (triple h.f y c).val).testBit h.f.val=true
    simp [Nat.testBit_xor,bit_pair,bit_triple,Ne.symm hhf.1,Ne.symm hhf.2.1,Ne.symm hhf.2.2.1,hyf]
  rcases selected_three_neighbors_repeat p hside hacy hbcy hbig adj1 adj2 adj3 with he | he | he
  · have hb := congrArg (fun z : Vertex => z.val.testBit a.val) he
    simp [bit_triple,Ne.symm h.outer.hab,Ne.symm h.outer.hac,hhy.1] at hb
  · have hb := congrArg (fun z : Vertex => z.val.testBit h.f.val) he
    dsimp only at hb
    rw [bigbit] at hb
    simp [bit_triple,Ne.symm hhf.1,Ne.symm hhf.2.2.1,hyf] at hb
  · have hb := congrArg (fun z : Vertex => z.val.testBit h.f.val) he
    dsimp only at hb
    rw [bigbit] at hb
    simp [bit_triple,Ne.symm hhf.2.1,Ne.symm hhf.2.2.1,hyf] at hb

end StarOuterConfig
#print axioms StarOuterConfig.residual_impossible
end
end Snake9
