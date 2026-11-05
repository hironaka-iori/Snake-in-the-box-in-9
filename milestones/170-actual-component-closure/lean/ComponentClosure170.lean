import CubeUndominated168
import PathClosure169

namespace Snake9.Component170

-- The two coordinate sets will be distinct components of the absent-pair graph.
def Cross (A B : Coord → Prop) (v : Vertex) : Prop :=
  ∃ a b, A a ∧ B b ∧ v = pair a b

def Family (A B : Coord → Prop) (v : Vertex) : Prop :=
  Cross A B v ∨ ∃ u w, Cross A B u ∧ Cross A B w ∧ u ≠ w ∧ Adj v u ∧ Adj v w

theorem cross_selected {m : Nat} (p : Snake m) (A B : Coord → Prop)
    (disjoint : ∀ a, A a → B a → False)
    (cutA : ∀ a k, A a → ¬ A k → InPath p (pair a k))
    {v : Vertex} (hv : Cross A B v) : InPath p v := by
  obtain ⟨a,b,ha,hb,rfl⟩ := hv
  exact cutA a b ha (fun hab => disjoint b hab hb)

theorem family_closed {m : Nat} (p : Snake m) (A B : Coord → Prop)
    (h0 : ∀ k : Coord, ¬ InPath p (unit k))
    (disjoint : ∀ a, A a → B a → False)
    (cutA : ∀ a k, A a → ¬ A k → InPath p (pair a k))
    (cutB : ∀ b k, B b → ¬ B k → InPath p (pair b k)) :
    ∀ u v, InPath p u → Family A B u → InPath p v → Adj u v → Family A B v := by
  intro u v hu hf hv hadj
  rcases hf with hc | ⟨x,y,hx,hy,hxy,hux,huy⟩
  · obtain ⟨a,b,ha,hb,rfl⟩ := hc
    obtain ⟨k,he⟩ := neighbor_pair a b hadj
    subst v
    have hk := Undominated168.selected_triple_distinct p h0 a b k hv
    have hab : a ≠ b := by
      intro h
      subst b
      exact disjoint a ha hb
    have sides := triple_adj_sides a b k
    by_cases hka : A k
    · right
      refine ⟨pair a b, pair b k, ⟨a,b,ha,hb,rfl⟩, ?_, ?_, sides.1, sides.2.2⟩
      · exact ⟨k,b,hka,hb,pair_comm b k⟩
      · intro heq
        rw [pair_comm a b] at heq
        exact hk.1 (pair_injective_right b a k heq).symm
    · have hkb : B k := by
        apply Classical.byContradiction
        intro hkb
        exact Undominated168.maximum_triple_neighbors p a b k hab hk.1 hk.2
          hv hu (cutA a k ha hka) (cutB b k hb hkb)
      right
      refine ⟨pair a b, pair a k, ⟨a,b,ha,hb,rfl⟩,
        ⟨a,k,ha,hkb,rfl⟩, ?_, sides.1, sides.2.1⟩
      intro heq
      exact hk.2 (pair_injective_right a b k heq).symm
  · have hsx := cross_selected p A B disjoint cutA hx
    have hsy := cross_selected p A B disjoint cutA hy
    rcases selected_three_neighbors_repeat p hu hsx hsy hv hux huy hadj with h | h | h
    · exact False.elim (hxy h)
    · exact Or.inl (h ▸ hx)
    · exact Or.inl (h ▸ hy)

theorem all_selected_in_family {m : Nat} (p : Snake m) (A B : Coord → Prop)
    (h0 : ∀ k : Coord, ¬ InPath p (unit k))
    (disjoint : ∀ a, A a → B a → False)
    (nonemptyA : ∃ a, A a) (nonemptyB : ∃ b, B b)
    (cutA : ∀ a k, A a → ¬ A k → InPath p (pair a k))
    (cutB : ∀ b k, B b → ¬ B k → InPath p (pair b k)) :
    ∀ v, InPath p v → Family A B v := by
  obtain ⟨a,ha⟩ := nonemptyA
  obtain ⟨b,hb⟩ := nonemptyB
  have hc : Cross A B (pair a b) := ⟨a,b,ha,hb,rfl⟩
  exact PathClosure169.closed_selected_contains_all p (Family A B)
    ⟨pair a b, cross_selected p A B disjoint cutA hc, Or.inl hc⟩
    (family_closed p A B h0 disjoint cutA cutB)

#print axioms cross_selected
#print axioms family_closed
#print axioms all_selected_in_family
end Snake9.Component170
