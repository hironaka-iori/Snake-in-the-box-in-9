import ComponentClosure170
import PairSupport170

namespace Snake9.Component170

theorem selected_pair_cross {m : Nat} (p : Snake m) (A B : Coord → Prop)
    (h0 : ∀ k : Coord, ¬ InPath p (unit k))
    (disjoint : ∀ a, A a → B a → False)
    (nonemptyA : ∃ a, A a) (nonemptyB : ∃ b, B b)
    (cutA : ∀ a k, A a → ¬ A k → InPath p (pair a k))
    (cutB : ∀ b k, B b → ¬ B k → InPath p (pair b k))
    (x y : Coord) (hxy : InPath p (pair x y)) : Cross A B (pair x y) := by
  have hf := all_selected_in_family p A B h0 disjoint nonemptyA nonemptyB cutA cutB
    (pair x y) hxy
  rcases hf with hc | ⟨u,v,hu,hv,hne,hau,hav⟩
  · exact hc
  · obtain ⟨a,b,ha,hb,rfl⟩ := hu
    exact False.elim (PairSupport170.pair_not_adjacent x y a b hau)

theorem two_coordinate_sets_cover {m : Nat} (p : Snake m) (A B : Coord → Prop)
    (h0 : ∀ k : Coord, ¬ InPath p (unit k))
    (disjoint : ∀ a, A a → B a → False)
    (nonemptyA : ∃ a, A a) (nonemptyB : ∃ b, B b)
    (cutA : ∀ a k, A a → ¬ A k → InPath p (pair a k))
    (cutB : ∀ b k, B b → ¬ B k → InPath p (pair b k)) :
    ∀ k, A k ∨ B k := by
  intro k
  by_cases hak : A k
  · exact Or.inl hak
  · right
    apply Classical.byContradiction
    intro hbk
    obtain ⟨a,ha⟩ := nonemptyA
    have hak' : a ≠ k := by intro he; subst k; exact hak ha
    have hs := cutA a k ha hak
    obtain ⟨x,y,hx,hy,he⟩ := selected_pair_cross p A B h0 disjoint
      ⟨a,ha⟩ nonemptyB cutA cutB a k hs
    have hxy : x ≠ y := by intro he; subst y; exact disjoint x hx hy
    rcases PairSupport170.pair_support_unique a k x y hak' hxy he with h | h
    · exact hbk (h.2 ▸ hy)
    · exact disjoint a ha (h.1.symm ▸ hy)

theorem first_coordinate_set_complete {m : Nat} (p : Snake m) (A B : Coord → Prop)
    (h0 : ∀ k : Coord, ¬ InPath p (unit k))
    (disjoint : ∀ a, A a → B a → False)
    (nonemptyA : ∃ a, A a) (nonemptyB : ∃ b, B b)
    (cutA : ∀ a k, A a → ¬ A k → InPath p (pair a k))
    (cutB : ∀ b k, B b → ¬ B k → InPath p (pair b k)) :
    ∀ a b, A a → A b → a ≠ b → ¬ InPath p (pair a b) := by
  intro a b ha hb hab hs
  obtain ⟨x,y,hx,hy,he⟩ := selected_pair_cross p A B h0 disjoint
    nonemptyA nonemptyB cutA cutB a b hs
  have hxy : x ≠ y := by intro he; subst y; exact disjoint x hx hy
  rcases PairSupport170.pair_support_unique a b x y hab hxy he with h | h
  · exact disjoint b hb (h.2.symm ▸ hy)
  · exact disjoint a ha (h.1.symm ▸ hy)

theorem second_coordinate_set_complete {m : Nat} (p : Snake m) (A B : Coord → Prop)
    (h0 : ∀ k : Coord, ¬ InPath p (unit k))
    (disjoint : ∀ a, A a → B a → False)
    (nonemptyA : ∃ a, A a) (nonemptyB : ∃ b, B b)
    (cutA : ∀ a k, A a → ¬ A k → InPath p (pair a k))
    (cutB : ∀ b k, B b → ¬ B k → InPath p (pair b k)) :
    ∀ a b, B a → B b → a ≠ b → ¬ InPath p (pair a b) := by
  exact first_coordinate_set_complete p B A h0 (fun a hb ha => disjoint a ha hb)
    nonemptyB nonemptyA cutB cutA

#print axioms selected_pair_cross
#print axioms two_coordinate_sets_cover
#print axioms first_coordinate_set_complete
#print axioms second_coordinate_set_complete
end Snake9.Component170
