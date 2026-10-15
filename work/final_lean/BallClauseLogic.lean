import PathStructure

namespace Snake9.BallClauseLogic

def Endpoint {m : Nat} (p : Snake m) (v : Vertex) : Prop :=
  InPath p v ∧ AtMostOneNeighbor p v

/-- The degree-at-most-two clauses used by the ball model are valid for a snake. -/
theorem degree_clause {m : Nat} (p : Snake m) (v a b c : Vertex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hva : Adj v a) (hvb : Adj v b) (hvc : Adj v c) :
    ¬ InPath p v ∨ ¬ InPath p a ∨ ¬ InPath p b ∨ ¬ InPath p c := by
  classical
  by_cases hv : InPath p v
  · by_cases ha : InPath p a
    · by_cases hb : InPath p b
      · right; right; right
        intro hc
        rcases selected_three_neighbors_repeat p hv ha hb hc hva hvb hvc with h | h | h
        · exact hab h
        · exact hac h
        · exact hbc h
      · exact Or.inr (Or.inr (Or.inl hb))
    · exact Or.inr (Or.inl ha)
  · exact Or.inl hv

/-- Three distinct vertices cannot all be endpoints. -/
theorem endpoint_triple_clause {m : Nat} (p : Snake m) (a b c : Vertex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Endpoint p a ∨ ¬ Endpoint p b ∨ ¬ Endpoint p c := by
  classical
  by_cases ha : Endpoint p a
  · by_cases hb : Endpoint p b
    · right; right
      intro hc
      rcases three_low_degree_vertices_repeat p ha.1 hb.1 hc.1 ha.2 hb.2 hc.2 with h | h | h
      · exact hab h
      · exact hac h
      · exact hbc h
    · exact Or.inr (Or.inl hb)
  · exact Or.inl ha

theorem endpoint_degree_clause {m : Nat} (p : Snake m) (v a b : Vertex)
    (hab : a ≠ b) (hva : Adj v a) (hvb : Adj v b) :
    ¬ Endpoint p v ∨ ¬ InPath p a ∨ ¬ InPath p b := by
  classical
  by_cases hv : Endpoint p v
  · by_cases ha : InPath p a
    · exact Or.inr (Or.inr (fun hb => hab (hv.2 a b ha hb hva hvb)))
    · exact Or.inr (Or.inl ha)
  · exact Or.inl hv

/-- Omitting one neighbor still leaves a selected neighbor unless the center
has at most one selected neighbor. -/
theorem other_neighbor_or_low {m : Nat} (p : Snake m) (v excluded : Vertex) :
    AtMostOneNeighbor p v ∨
      ∃ w, w ≠ excluded ∧ InPath p w ∧ Adj v w := by
  classical
  by_cases hl : AtMostOneNeighbor p v
  · exact Or.inl hl
  · right
    apply Classical.byContradiction
    intro h
    apply hl
    intro a b ha hb hva hvb
    have hea : a = excluded := by
      apply Classical.byContradiction
      intro he
      exact h ⟨a, he, ha, hva⟩
    have heb : b = excluded := by
      apply Classical.byContradiction
      intro he
      exact h ⟨b, he, hb, hvb⟩
    exact hea.trans heb.symm

/-- A list covering every neighbor except one gives the lower-degree clause. -/
theorem neighbor_list_clause {m : Nat} (p : Snake m) (v excluded : Vertex)
    (others : List Vertex)
    (hcover : ∀ w, Adj v w → w ≠ excluded → w ∈ others) :
    ¬ InPath p v ∨ Endpoint p v ∨ ∃ w ∈ others, InPath p w := by
  classical
  by_cases hv : InPath p v
  · rcases other_neighbor_or_low p v excluded with hl | ⟨w, hw, hs, ha⟩
    · exact Or.inr (Or.inl ⟨hv, hl⟩)
    · exact Or.inr (Or.inr ⟨w, hcover w ha hw, hs⟩)
  · exact Or.inl hv

theorem internal_neighbor_list_clause {m : Nat} (p : Snake m) (v excluded : Vertex)
    (others : List Vertex)
    (hcover : ∀ w, Adj v w → w ≠ excluded → w ∈ others)
    (hinternal : ¬ AtMostOneNeighbor p v) :
    ∃ w ∈ others, InPath p w := by
  rcases other_neighbor_or_low p v excluded with hl | ⟨w, hw, hs, ha⟩
  · exact False.elim (hinternal hl)
  · exact ⟨w, hcover w ha hw, hs⟩

#print axioms degree_clause
#print axioms endpoint_triple_clause
#print axioms endpoint_degree_clause
#print axioms other_neighbor_or_low
#print axioms neighbor_list_clause
#print axioms internal_neighbor_list_clause
end Snake9.BallClauseLogic
