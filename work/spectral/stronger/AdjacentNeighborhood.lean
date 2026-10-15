import AdjacentConfiguration
import CubeCoordinateAlgebra

namespace Snake9
set_option maxHeartbeats 600000
set_option maxRecDepth 100000

namespace AdjacentConfig
variable {m : Nat} {p : Snake m} {a b c d e : Coord} (h : AdjacentConfig p a b c d e)
include h

theorem selected_abk (k : Coord) (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hke : k≠e) :
    InPath p (triple a b k) := by
  apply h.selected_triple b k (Ne.symm hkb) (Ne.symm h.hab) h.hbc hka hkc
  simp [hke,h.hbe]

theorem selected_aek (k : Coord) (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hke : k≠e) :
    InPath p (triple a e k) := by
  apply h.selected_triple e k (Ne.symm hke) (Ne.symm h.hae) (Ne.symm h.hce) hka hkc
  simp [Ne.symm h.hbe,hkb]

theorem triple_neighbor_cover (k : Coord)
    (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hkd : k≠d) (hke : k≠e) :
    ∀ w, InPath p w → Adj (triple a b k) w →
      w=quad a b c k ∨ w=quad a b e k := by
  intro w hw hadj
  obtain ⟨x,rfl⟩ := neighbor_triple a b k hadj
  by_cases hxa : x=a
  · subst x
    rw [quad_cancel_first] at hw
    exact False.elim (h.absent_pair_bk k hka hkb hkc hkd hw)
  by_cases hxb : x=b
  · subst x
    rw [quad_cancel_second] at hw
    exact False.elim (h.absent_pair_ak k hka hkc hw)
  by_cases hxk : x=k
  · subst x
    rw [quad_cancel_third] at hw
    exact False.elim (h.absent_pair_ak b (Ne.symm h.hab) h.hbc hw)
  by_cases hxc : x=c
  · subst x
    exact Or.inl (quad_swap_last _ _ _ _)
  by_cases hxe : x=e
  · subst x
    exact Or.inr (quad_swap_last _ _ _ _)
  have ht := h.selected_abk k hka hkb hkc hke
  have hx := h.selected_abk x hxa hxb hxc hxe
  have hkx : InPath p (triple a k x) := by
    apply h.selected_triple k x (Ne.symm hxk) hka hkc hxa hxc
    simp [hkb,hke]
  have hadj0 : Adj (quad a b k x) (triple a b k) := adj_symmetric (triple_quad_adj _ _ _ _)
  have hadj1 : Adj (quad a b k x) (triple a b x) := by
    rw [quad_swap_last]
    exact adj_symmetric (triple_quad_adj _ _ _ _)
  have heq : quad a b k x = quad a k x b := by
    apply Fin.ext
    dsimp [quad,triple,pair,vxor]
    ac_rfl
  have hadj2 : Adj (quad a b k x) (triple a k x) := by
    rw [heq]
    exact adj_symmetric (triple_quad_adj _ _ _ _)
  rcases selected_three_neighbors_repeat p hw ht hx hkx hadj0 hadj1 hadj2 with he | he | he
  · exact False.elim (hxk (triple_injective_right a b k x he).symm)
  · have hb := congrArg (fun v : Vertex => v.val.testBit b.val) he
    simp [bit_triple,h.hab,hkb,hxb] at hb
  · rw [triple_swap a b x,triple_swap a k x] at he
    exact False.elim (hkb (triple_injective_right a x b k he).symm)

theorem selected_abek_excludes_bek (k : Coord)
    (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hke : k≠e)
    (hq : InPath p (quad a b e k)) : ¬ InPath p (triple b e k) := by
  intro hz
  have ht := h.selected_abk k hka hkb hkc hke
  have hu := h.selected_aek k hka hkb hkc hke
  have he0 : quad a b e k = quad a b k e := quad_swap_last _ _ _ _
  have he1 : quad a b e k = quad a e k b := by
    apply Fin.ext
    dsimp [quad,triple,pair,vxor]
    ac_rfl
  have he2 : quad a b e k = quad b e k a := (quad_rotate _ _ _ _).symm
  have h0 : Adj (quad a b e k) (triple a b k) := by
    rw [he0]; exact adj_symmetric (triple_quad_adj _ _ _ _)
  have h1 : Adj (quad a b e k) (triple a e k) := by
    rw [he1]; exact adj_symmetric (triple_quad_adj _ _ _ _)
  have h2 : Adj (quad a b e k) (triple b e k) := by
    rw [he2]; exact adj_symmetric (triple_quad_adj _ _ _ _)
  rcases selected_three_neighbors_repeat p hq ht hu hz h0 h1 h2 with he | he | he
  · rw [triple_swap a b k,triple_swap a e k] at he
    exact h.hbe (triple_injective_right a k b e he)
  · have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    simp [bit_triple,Ne.symm h.hab,Ne.symm h.hae,hka] at hb
  · have hb := congrArg (fun v : Vertex => v.val.testBit a.val) he
    simp [bit_triple,Ne.symm h.hab,Ne.symm h.hae,hka] at hb

end AdjacentConfig
#print axioms AdjacentConfig.triple_neighbor_cover
#print axioms AdjacentConfig.selected_abek_excludes_bek
end Snake9
