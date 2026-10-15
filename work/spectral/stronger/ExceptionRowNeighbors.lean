import AdjacentConfiguration
import CubeCoordinateAlgebra

namespace Snake9
set_option maxHeartbeats 500000

theorem forced_pairs_except_swap {m : Nat} (p : Snake m) (c d : Coord)
    (h : ForcedPairsExcept p c d) : ForcedPairsExcept p d c := by
  intro i j hij hi hj hn
  apply h i j hij hi hj
  intro he
  exact hn he.symm

theorem exception_row_cover {m : Nat} (p : Snake m) (a b c d k : Coord)
    (hca : c≠a) (hcb : c≠b) (hcd : c≠d)
    (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hkd : k≠d)
    (cover : ∀ i, InPath p (unit i) → i=a ∨ i=b)
    (forced : ForcedPairsExcept p c d) :
    ∀ w, InPath p w → Adj (pair c k) w →
      w=triple a c k ∨ w=triple b c k ∨ w=triple c d k := by
  have absent (i : Coord) (hia : i≠a) (hib : i≠b) : ¬ InPath p (unit i) := by
    intro hi
    rcases cover i hi with he | he
    · exact hia he
    · exact hib he
  intro w hw hadj
  obtain ⟨i,rfl⟩ := neighbor_pair c k hadj
  by_cases hic : i=c
  · subst i
    rw [triple_cancel_left] at hw
    exact False.elim (absent k hka hkb hw)
  by_cases hik : i=k
  · subst i
    rw [triple_cancel_right] at hw
    exact False.elim (absent c hca hcb hw)
  by_cases hia : i=a
  · subst i
    exact Or.inl (triple_rotate c k a)
  by_cases hib : i=b
  · subst i
    exact Or.inr (Or.inl (triple_rotate c k b))
  by_cases hid : i=d
  · subst i
    exact Or.inr (Or.inr (triple_swap c k d))
  have hck : InPath p (pair c k) := forced c k (Ne.symm hkc)
    (absent c hca hcb) (absent k hka hkb) (by simp [hkd,hcd])
  have hci : InPath p (pair c i) := forced c i (Ne.symm hic)
    (absent c hca hcb) (absent i hia hib) (by simp [hid,hcd])
  have hki : InPath p (pair k i) := forced k i (Ne.symm hik)
    (absent k hka hkb) (absent i hia hib) (by simp [hkc,hkd])
  exact False.elim (selected_triple_forbidden p c k i (Ne.symm hkc)
    (Ne.symm hic) (Ne.symm hik) hck hci hki hw)

namespace AdjacentConfig
variable {m : Nat} {p : Snake m} {a b c d : Coord} (h : AdjacentConfig p a b c d d)
include h

theorem row_d_neighbors (k : Coord)
    (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hkd : k≠d)
    (missing : ¬ InPath p (triple b d k)) :
    ∀ w, InPath p w → Adj (pair d k) w →
      w=triple a d k ∨ w=triple c d k := by
  intro w hw hadj
  rcases exception_row_cover p a b d c k (Ne.symm h.had) (Ne.symm h.hbd)
      (Ne.symm h.hcd) hka hkb hkd hkc h.cover
      (forced_pairs_except_swap p c d h.forced) w hw hadj with he | he | he
  · exact Or.inl he
  · exact False.elim (missing (he ▸ hw))
  · right
    rw [he]
    apply Fin.ext
    dsimp [triple,pair,vxor]
    ac_rfl

theorem row_c_neighbors (k : Coord)
    (hka : k≠a) (hkb : k≠b) (hkc : k≠c) (hkd : k≠d) :
    ∀ w, InPath p w → Adj (pair c k) w →
      w=triple b c k ∨ w=triple c d k := by
  intro w hw hadj
  rcases exception_row_cover p a b c d k (Ne.symm h.hac) (Ne.symm h.hbc)
      h.hcd hka hkb hkc hkd h.cover h.forced w hw hadj with he | he | he
  · exact False.elim (h.absent_triple_ack k hka hkb hkc hkd (he ▸ hw))
  · exact Or.inl he
  · exact Or.inr he

end AdjacentConfig
#print axioms exception_row_cover
#print axioms AdjacentConfig.row_d_neighbors
#print axioms AdjacentConfig.row_c_neighbors
end Snake9
