import ComponentClassification170

namespace Snake9.Component170

def MissingEdge {m : Nat} (p : Snake m) (a b : Coord) : Prop :=
  a ≠ b ∧ ¬ InPath p (pair a b)

inductive MissingReach {m : Nat} (p : Snake m) : Coord → Coord → Prop
  | refl (a) : MissingReach p a a
  | step {a b c} : MissingReach p a b → MissingEdge p b c → MissingReach p a c

theorem missing_edge_symm {m : Nat} (p : Snake m) {a b : Coord}
    (h : MissingEdge p a b) : MissingEdge p b a := by
  refine ⟨Ne.symm h.1, ?_⟩
  intro hs
  exact h.2 (by simpa only [pair_comm b a] using hs)

theorem reach_cut {m : Nat} (p : Snake m) (root : Coord) :
    ∀ a k, MissingReach p root a → ¬ MissingReach p root k → InPath p (pair a k) := by
  intro a k ha hk
  apply Classical.byContradiction
  intro hs
  have hak : a ≠ k := by intro he; subst k; exact hk ha
  exact hk (MissingReach.step ha ⟨hak,hs⟩)

theorem complement_reach_cut {m : Nat} (p : Snake m) (root : Coord) :
    ∀ b k, ¬ MissingReach p root b → ¬ (¬ MissingReach p root k) → InPath p (pair b k) := by
  intro b k hb hk
  have hk' : MissingReach p root k := Classical.byContradiction hk
  have hs := reach_cut p root k b hk' hb
  simpa only [pair_comm k b] using hs

theorem missing_component_complete {m : Nat} (p : Snake m)
    (h0 : ∀ k : Coord, ¬ InPath p (unit k))
    (root outside : Coord) (hout : ¬ MissingReach p root outside) :
    ∀ a b, MissingReach p root a → MissingReach p root b → a ≠ b →
      ¬ InPath p (pair a b) := by
  exact first_coordinate_set_complete p (MissingReach p root) (fun k => ¬ MissingReach p root k)
    h0 (fun _ ha hb => hb ha) ⟨root,MissingReach.refl root⟩ ⟨outside,hout⟩
    (reach_cut p root) (complement_reach_cut p root)

theorem missing_complement_complete {m : Nat} (p : Snake m)
    (h0 : ∀ k : Coord, ¬ InPath p (unit k))
    (root outside : Coord) (hout : ¬ MissingReach p root outside) :
    ∀ a b, ¬ MissingReach p root a → ¬ MissingReach p root b → a ≠ b →
      ¬ InPath p (pair a b) := by
  exact second_coordinate_set_complete p (MissingReach p root) (fun k => ¬ MissingReach p root k)
    h0 (fun _ ha hb => hb ha) ⟨root,MissingReach.refl root⟩ ⟨outside,hout⟩
    (reach_cut p root) (complement_reach_cut p root)

-- This specifies every off-diagonal edge of the actual missing-pair graph.
theorem disconnected_missing_graph_exact {m : Nat} (p : Snake m)
    (h0 : ∀ k : Coord, ¬ InPath p (unit k))
    (root outside : Coord) (hout : ¬ MissingReach p root outside) :
    ∀ a b, a ≠ b →
      (MissingEdge p a b ↔ (MissingReach p root a ↔ MissingReach p root b)) := by
  intro a b hab
  constructor
  · intro he
    constructor
    · intro ha
      exact MissingReach.step ha he
    · intro hb
      exact MissingReach.step hb (missing_edge_symm p he)
  · intro he
    refine ⟨hab, ?_⟩
    by_cases ha : MissingReach p root a
    · exact missing_component_complete p h0 root outside hout a b ha (he.mp ha) hab
    · have hb : ¬ MissingReach p root b := fun hb => ha (he.mpr hb)
      exact missing_complement_complete p h0 root outside hout a b ha hb hab

-- An arbitrary undominated center is moved to zero without changing the path.
theorem translated_units_absent {m : Nat} (p : Snake m) (q : Vertex)
    (hq : ∀ v, InPath p v → ¬ Adj q v) :
    ∀ a : Coord, ¬ InPath (translate p q) (unit a) := by
  intro a hs
  obtain ⟨i,hi⟩ := hs
  have he : vxor q (p.vertex i) = unit a := hi
  have hz : Adj (vxor q q) (vxor q (p.vertex i)) := by
    rw [vxor_self, he]
    exact (adj_zero_iff (unit a)).mpr ⟨a,rfl⟩
  exact hq (p.vertex i) ⟨i,rfl⟩ ((adj_vxor q q (p.vertex i)).mp hz)

theorem translated_disconnected_missing_graph_exact {m : Nat} (p : Snake m)
    (q : Vertex) (hq : ∀ v, InPath p v → ¬ Adj q v)
    (root outside : Coord) (hout : ¬ MissingReach (translate p q) root outside) :
    ∀ a b, a ≠ b →
      (MissingEdge (translate p q) a b ↔
        (MissingReach (translate p q) root a ↔ MissingReach (translate p q) root b)) := by
  exact disconnected_missing_graph_exact (translate p q) (translated_units_absent p q hq)
    root outside hout

#print axioms reach_cut
#print axioms complement_reach_cut
#print axioms missing_component_complete
#print axioms missing_complement_complete
#print axioms disconnected_missing_graph_exact
#print axioms translated_units_absent
#print axioms translated_disconnected_missing_graph_exact
end Snake9.Component170
