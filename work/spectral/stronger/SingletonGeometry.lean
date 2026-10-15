import SingletonSquareLemma
import FreshCoordinates

namespace Snake9
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

/- Every missing pair of absent unit vertices is the same unordered pair c,d. -/
def ForcedPairsExcept {m : Nat} (p : Snake m) (c d : Coord) : Prop :=
  ∀ i j : Coord, i ≠ j → ¬ InPath p (unit i) → ¬ InPath p (unit j) →
    ¬ ((i=c ∧ j=d) ∨ (i=d ∧ j=c)) → InPath p (pair i j)

theorem missing_candidate_low_degree_except {m : Nat} (p : Snake m)
    (a b c d i j : Coord)
    (hia : i≠a) (hib : i≠b) (hic : i≠c) (hid : i≠d)
    (hja : j≠a) (hjb : j≠b) (hjc : j≠c) (hjd : j≠d) (hij : i≠j)
    (cover : ∀ k : Coord, InPath p (unit k) → k=a ∨ k=b)
    (forced : ForcedPairsExcept p c d) (missing : ¬ InPath p (triple a i j)) :
    AtMostOneNeighbor p (pair i j) := by
  have absent (k : Coord) (hka : k≠a) (hkb : k≠b) : ¬ InPath p (unit k) := by
    intro hk
    rcases cover k hk with h | h
    · exact hka h
    · exact hkb h
  have force_i (k : Coord) (hik : i≠k) (hka : k≠a) (hkb : k≠b) :
      InPath p (pair i k) :=
    forced i k hik (absent i hia hib) (absent k hka hkb) (by simp [hic,hid])
  have force_j (k : Coord) (hjk : j≠k) (hka : k≠a) (hkb : k≠b) :
      InPath p (pair j k) :=
    forced j k hjk (absent j hja hjb) (absent k hka hkb) (by simp [hjc,hjd])
  have unique (v : Vertex) (hv : InPath p v) (hadj : Adj (pair i j) v) : v=triple i j b := by
    obtain ⟨k,rfl⟩ := neighbor_pair i j hadj
    by_cases hki : k=i
    · subst k
      rw [triple_cancel_left] at hv
      exact False.elim (absent j hja hjb hv)
    by_cases hkj : k=j
    · subst k
      rw [triple_cancel_right] at hv
      exact False.elim (absent i hia hib hv)
    by_cases hka : k=a
    · subst k
      rw [triple_rotate] at hv
      exact False.elim (missing hv)
    by_cases hkb : k=b
    · exact congrArg (triple i j) hkb
    exact False.elim (selected_triple_forbidden p i j k hij (Ne.symm hki) (Ne.symm hkj)
      (force_i j hij hja hjb)
      (force_i k (Ne.symm hki) hka hkb)
      (force_j k (Ne.symm hkj) hka hkb) hv)
  intro v w hv hw hadjv hadjw
  exact (unique v hv hadjv).trans (unique w hw hadjw).symm

theorem arm_outside_missing_impossible {m : Nat} (p : Snake m)
    (a b c d i : Coord) (hai : a≠i) (hbi : b≠i) (hic : i≠c) (hid : i≠d)
    (ha : InPath p (unit a)) (hc : InPath p (pair a i))
    (cover : ∀ k : Coord, InPath p (unit k) → k=a ∨ k=b)
    (forced : ForcedPairsExcept p c d)
    (j : Fin 4 → Coord)
    (outside : ∀ k, j k≠a ∧ j k≠b ∧ j k≠i ∧ j k≠c ∧ j k≠d)
    (distinct : ∀ k l, j k=j l → k=l) : False := by
  have absent (k : Coord) (hka : k≠a) (hkb : k≠b) : ¬ InPath p (unit k) := by
    intro hk
    rcases cover k hk with h | h
    · exact hka h
    · exact hkb h
  apply four_candidates_impossible p (fun k => pair i (j k)) (fun k => triple a i (j k))
  · intro k
    exact forced i (j k) (Ne.symm (outside k).2.2.1)
      (absent i (Ne.symm hai) (Ne.symm hbi))
      (absent (j k) (outside k).1 (outside k).2.1) (by simp [hic,hid])
  · intro k l h
    exact distinct k l (pair_injective_right i (j k) (j l) h)
  · intro k l hk hl
    rcases selected_three_neighbors_repeat p hc ha hk hl
      (adj_symmetric (unit_pair_adj a i)) (pair_triple_adj a i (j k))
      (pair_triple_adj a i (j l)) with h | h | h
    · exact False.elim (triple_ne_unit a i (j k) (Ne.symm (outside k).2.2.1) h.symm)
    · exact False.elim (triple_ne_unit a i (j l) (Ne.symm (outside l).2.2.1) h.symm)
    · exact distinct k l (triple_injective_right a i (j k) (j l) h)
  · intro k hk
    exact missing_candidate_low_degree_except p a b c d i (j k)
      (Ne.symm hai) (Ne.symm hbi) hic hid (outside k).1 (outside k).2.1
      (outside k).2.2.2.1 (outside k).2.2.2.2 (Ne.symm (outside k).2.2.1)
      cover forced hk

#print axioms missing_candidate_low_degree_except
#print axioms arm_outside_missing_impossible

theorem arm_coordinate_in_missing {m : Nat} (p : Snake m)
    (a b c d i : Coord) (hai : a≠i) (hbi : b≠i)
    (ha : InPath p (unit a)) (hc : InPath p (pair a i))
    (cover : ∀ k : Coord, InPath p (unit k) → k=a ∨ k=b)
    (forced : ForcedPairsExcept p c d) : i=c ∨ i=d := by
  by_contra h
  have hic : i≠c := fun he => h (Or.inl he)
  have hid : i≠d := fun he => h (Or.inr he)
  obtain ⟨j,hj,hji⟩ := exists_four_coords_outside_five a b i c d
  exact arm_outside_missing_impossible p a b c d i hai hbi hic hid ha hc cover forced
    j hj (fun k l he => hji he)

#print axioms arm_coordinate_in_missing
end Snake9
