import CubeLocal
import Undominated167

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Snake9.Undominated168

-- These statements concern an actual induced path in Q9, centered at zero.
-- h0 says that zero has no selected neighbor; it does not assume zero absent.
theorem selected_neighbor {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    {v : Vertex} (hv : InPath p v) :
    ∃ w, InPath p w ∧ Adj v w := by
  obtain ⟨i, rfl⟩ := hv
  have hib := i.isLt
  by_cases hi : i.val < m
  · let j : Fin (m + 1) := ⟨i.val + 1, by omega⟩
    exact ⟨p.vertex j, ⟨j, rfl⟩, (path_adj_iff p i j).mpr (Or.inl rfl)⟩
  · let j : Fin (m + 1) := ⟨i.val - 1, by omega⟩
    refine ⟨p.vertex j, ⟨j, rfl⟩, (path_adj_iff p i j).mpr (Or.inr ?_)⟩
    dsimp [j]
    omega

theorem selected_triple_distinct {m : Nat} (p : Snake m)
    (h0 : ∀ i : Coord, ¬ InPath p (unit i))
    (a b k : Coord) (ht : InPath p (triple a b k)) : k ≠ a ∧ k ≠ b := by
  constructor
  · intro he
    subst k
    exact h0 b (by simpa only [triple_cancel_left] using ht)
  · intro he
    subst k
    exact h0 a (by simpa only [triple_cancel_right] using ht)

theorem minimum_pair_neighbor {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (h0 : ∀ i : Coord, ¬ InPath p (unit i)) :
    ∀ a b : Coord, a ≠ b → InPath p (pair a b) →
      ∃ k, k ≠ a ∧ k ≠ b ∧ InPath p (triple a b k) := by
  intro a b _ hp
  obtain ⟨v, hv, hadj⟩ := selected_neighbor p hm hp
  obtain ⟨k, he⟩ := neighbor_pair a b hadj
  have ht : InPath p (triple a b k) := he ▸ hv
  have hk := selected_triple_distinct p h0 a b k ht
  exact ⟨k, hk.1, hk.2, ht⟩

theorem maximum_triple_neighbors {m : Nat} (p : Snake m) :
    ∀ a b k : Coord, a ≠ b → k ≠ a → k ≠ b →
      InPath p (triple a b k) → InPath p (pair a b) →
      InPath p (pair a k) → InPath p (pair b k) → False := by
  intro a b k hab hka hkb ht habp hakp hbkp
  have hadj := triple_adj_sides a b k
  have hne := three_pairs_distinct a b k hab (Ne.symm hka) (Ne.symm hkb)
  rcases selected_three_neighbors_repeat p ht habp hakp hbkp
      hadj.1 hadj.2.1 hadj.2.2 with h | h | h
  · exact hne.1 h
  · exact hne.2.1 h
  · exact hne.2.2 h

-- A direction is unused by the absent-pair graph precisely when every
-- pair vertex involving that direction and a different direction is selected.
theorem no_two_unused_directions {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (h0 : ∀ i : Coord, ¬ InPath p (unit i))
    (a b : Coord) (hab : a ≠ b)
    (ha : ∀ k, k ≠ a → InPath p (pair a k))
    (hb : ∀ k, k ≠ b → InPath p (pair b k)) : False := by
  exact Undominated167.no_two_unused
    (fun i j => InPath p (pair i j))
    (fun i j k => InPath p (triple i j k))
    (minimum_pair_neighbor p hm h0) (maximum_triple_neighbors p)
    a b hab ha hb

-- Under a matching pattern of absent pairs, the selected pair c,a has
-- exactly one possible selected neighbor. Hence it is a path endpoint.
theorem matching_pair_low_degree {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (h0 : ∀ i : Coord, ¬ InPath p (unit i))
    (c a partner : Coord) (hca : c ≠ a)
    (hc : ∀ k, k ≠ c → InPath p (pair c k))
    (ha : ∀ k, k ≠ a → k ≠ partner → InPath p (pair a k)) :
    InPath p (pair c a) ∧ AtMostOneNeighbor p (pair c a) := by
  have hk := Undominated167.matching_forces_unique_neighbor
    (fun i j => InPath p (pair i j))
    (fun i j k => InPath p (triple i j k))
    (minimum_pair_neighbor p hm h0) (maximum_triple_neighbors p)
    c a partner hca hc ha
  refine ⟨hc a (Ne.symm hca), ?_⟩
  intro v w hv hw hav haw
  obtain ⟨i, hi⟩ := neighbor_pair c a hav
  obtain ⟨j, hj⟩ := neighbor_pair c a haw
  have hti : InPath p (triple c a i) := hi ▸ hv
  have htj : InPath p (triple c a j) := hj ▸ hw
  have hdi := selected_triple_distinct p h0 c a i hti
  have hdj := selected_triple_distinct p h0 c a j htj
  have hip := hk.2 i hdi.1 hdi.2 hti
  have hjp := hk.2 j hdj.1 hdj.2 htj
  calc
    v = triple c a i := hi
    _ = triple c a partner := congrArg (triple c a) hip
    _ = triple c a j := congrArg (triple c a) hjp.symm
    _ = w := hj.symm

-- Only three forced endpoint pairs are needed for the final contradiction.
-- Counting eight endpoints is therefore unnecessary in the cube bridge.
theorem three_matching_pairs_impossible {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (h0 : ∀ i : Coord, ¬ InPath p (unit i))
    (c a b d : Coord) (partner : Coord → Coord)
    (hca : c ≠ a) (hcb : c ≠ b) (hcd : c ≠ d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hc : ∀ k, k ≠ c → InPath p (pair c k))
    (ha : ∀ k, k ≠ a → k ≠ partner a → InPath p (pair a k))
    (hb : ∀ k, k ≠ b → k ≠ partner b → InPath p (pair b k))
    (hd : ∀ k, k ≠ d → k ≠ partner d → InPath p (pair d k)) : False := by
  have hA := matching_pair_low_degree p hm h0 c a (partner a) hca hc ha
  have hB := matching_pair_low_degree p hm h0 c b (partner b) hcb hc hb
  have hD := matching_pair_low_degree p hm h0 c d (partner d) hcd hc hd
  rcases three_low_degree_vertices_repeat p hA.1 hB.1 hD.1
      hA.2 hB.2 hD.2 with h | h | h
  · exact hab (pair_injective_right c a b h)
  · exact had (pair_injective_right c a d h)
  · exact hbd (pair_injective_right c b d h)

#print axioms selected_neighbor
#print axioms selected_triple_distinct
#print axioms minimum_pair_neighbor
#print axioms maximum_triple_neighbors
#print axioms no_two_unused_directions
#print axioms matching_pair_low_degree
#print axioms three_matching_pairs_impossible

end Snake9.Undominated168
