import GeneralOneTwoLocal

namespace Snake9
open SquareIncidence
set_option maxHeartbeats 1000000

theorem selected_flip_forbidden {m : Nat} (p : Snake m)
    (v : Vertex) (a b c : Coord) (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (hv : InPath p v) (ha : InPath p (flip a v)) (hb : InPath p (flip b v)) :
    ¬InPath p (flip c v) := by
  intro hc
  rcases selected_three_neighbors_repeat p hv ha hb hc
    (flip_adj a v) (flip_adj b v) (flip_adj c v) with he | he | he
  · exact hab (flip_inj_coord v he)
  · exact hac (flip_inj_coord v he)
  · exact hbc (flip_inj_coord v he)

theorem two_layer_saturation {m : Nat} (p : Snake m) (a b i j k : Coord)
    (hab : a≠b) (hka : k≠a) (hkb : k≠b)
    (hij : InPath p (pair i j)) (habij : InPath p (quad a b i j))
    (haij : InPath p (triple a i j)) : ¬InPath p (quad a i j k) := by
  have he0 : flip a (triple a i j)=pair i j := by
    change quad a i j a=pair i j
    exact quad_cancel_first _ _ _
  have he1 : flip b (triple a i j)=quad a b i j := by
    apply Fin.ext; dsimp [SquareIncidence.flip,quad,triple,pair,vxor]; ac_rfl
  have hx := selected_flip_forbidden p (triple a i j) a b k hab
    (Ne.symm hka) (Ne.symm hkb) haij (he0.symm ▸ hij) (he1.symm ▸ habij)
  exact hx

#print axioms selected_flip_forbidden
#print axioms two_layer_saturation
end Snake9
