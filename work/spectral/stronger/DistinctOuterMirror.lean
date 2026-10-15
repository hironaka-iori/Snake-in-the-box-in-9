import DistinctOuterClassification

namespace Snake9
open SquareIncidence Finset Classical
noncomputable section
set_option maxHeartbeats 1800000

theorem translate_middle_triple (p : Snake m) (a b i j : Coord) :
    InPath (translate p (pair a b)) (triple b i j) ↔ InPath p (triple a i j) := by
  rw [inPath_translate_at]
  have he : vxor (pair a b) (triple b i j)=triple a i j := by
    apply Fin.ext
    change ((unit a).val ^^^ (unit b).val) ^^^ (((unit b).val ^^^ (unit i).val) ^^^ (unit j).val) = _
    calc
      _ = (((unit a).val ^^^ (unit i).val) ^^^ (unit j).val) ^^^ ((unit b).val ^^^ (unit b).val) := by ac_rfl
      _ = _ := by rw [Nat.xor_self,Nat.xor_zero]; rfl
  rw [he]

def MissingAtNeighbor.mirror {m : Nat} {p : Snake m} {a b : Coord}
    (f : MissingAtNeighbor p a b) : MissingAtNeighbor (translate p (pair a b)) b a where
  F := f.F
  edge_card := f.edge_card
  avoids := fun s hs k hk => (f.avoids s hs k hk).symm
  selected_iff := by
    intro i j hij hib hia hjb hja
    rw [translate_middle_triple]
    exact f.selected_iff i j hij hia hib hja hjb

namespace DistinctOuterConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : DistinctOuterConfig p a b c d)
include h

def mirror : DistinctOuterConfig (translate p (pair a b)) b a d c := by
  let q := translate p (pair a b)
  have h0 : InPath q 0 := by rw [inPath_translate_at,vxor_zero]; exact h.hab_selected
  have hb : InPath q (unit b) := by
    rw [inPath_translate_at]
    change InPath p (triple a b b)
    simpa only [triple_cancel_right] using h.ha
  have hd : InPath q (unit d) := (inPath_translate_at p _ _).mpr h.habd_selected
  have hba : InPath q (pair b a) := by
    rw [inPath_translate_at,pair_comm b a,vxor_self]
    exact h.hzero
  have hbac : InPath q (triple b a c) := by
    rw [inPath_translate_at,triple_swap b a c,triple_rotate b c a]
    change InPath p (vxor (pair a b) (triple a b c))
    change InPath p (vxor (pair a b) (vxor (pair a b) (unit c)))
    rw [vxor_cancel]
    exact h.hc
  have double_mem (v : Vertex) : InPath (translate q (pair b a)) v ↔ InPath p v := by
    change InPath (translate (translate p (pair a b)) (pair b a)) v ↔ InPath p v
    rw [inPath_translate_at,inPath_translate_at,pair_comm b a,vxor_cancel]
  let right : TwoMissingAtZero (translate q (pair b a)) a c := {
    F:=h.left.F, Fcard:=h.left.Fcard, edge_card:=h.left.edge_card, avoids:=h.left.avoids,
    selected_iff:=by
      intro i j hij hia hic hja hjc
      rw [double_mem]
      exact h.left.selected_iff i j hij hia hic hja hjc }
  exact ⟨Ne.symm h.hab,h.hbd,h.hbc,h.had,h.hac,Ne.symm h.hcd,
    h0,hb,hd,hba,hbac,h.right,right⟩

theorem opposite_delta_impossible (hbd : ({b,d}:Finset Coord)∉h.left.F)
    (hac : ({a,c}:Finset Coord)∈h.right.F)
    (f : MissingAtNeighbor p a b) (hFcard : f.F.card=2) : False := by
  exact h.mirror.single_delta_impossible hac hbd f.mirror hFcard

end DistinctOuterConfig
#print axioms DistinctOuterConfig.mirror
#print axioms DistinctOuterConfig.opposite_delta_impossible
end
end Snake9
