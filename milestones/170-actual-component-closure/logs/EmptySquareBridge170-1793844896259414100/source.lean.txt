import MissingComponents170

namespace Snake9.Component170

theorem in_translate_iff {m : Nat} (p : Snake m) (q v : Vertex) :
    InPath (translate p q) v ↔ InPath p (vxor q v) := by
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨i, ?_⟩
    have hh := congrArg (vxor q) hi
    change vxor q (vxor q (p.vertex i)) = vxor q v at hh
    simpa only [vxor_cancel] using hh
  · rintro ⟨i,hi⟩
    refine ⟨i, ?_⟩
    change vxor q (p.vertex i) = v
    rw [hi, vxor_cancel]

theorem undominated_center_absent {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (q : Vertex) (hq : ∀ v, InPath p v → ¬ Adj q v) : ¬ InPath p q := by
  intro hs
  obtain ⟨v,hv,ha⟩ := Undominated168.selected_neighbor p hm hs
  exact hq v hv ha

theorem empty_square_missing_edge_iff {m : Nat} (p : Snake m) (hm : 1 ≤ m)
    (q : Vertex) (hq : ∀ v, InPath p v → ¬ Adj q v)
    (a b : Coord) (hab : a ≠ b) :
    (¬ InPath p q ∧ ¬ InPath p (vxor q (unit a)) ∧
      ¬ InPath p (vxor q (unit b)) ∧ ¬ InPath p (vxor q (pair a b))) ↔
      MissingEdge (translate p q) a b := by
  constructor
  · intro he
    refine ⟨hab, ?_⟩
    intro hs
    exact he.2.2.2 ((in_translate_iff p q (pair a b)).mp hs)
  · intro he
    refine ⟨undominated_center_absent p hm q hq, ?_, ?_, ?_⟩
    · intro hs
      exact translated_units_absent p q hq a ((in_translate_iff p q (unit a)).mpr hs)
    · intro hs
      exact translated_units_absent p q hq b ((in_translate_iff p q (unit b)).mpr hs)
    · intro hs
      exact he.2 ((in_translate_iff p q (pair a b)).mpr hs)

#print axioms in_translate_iff
#print axioms undominated_center_absent
#print axioms empty_square_missing_edge_iff
end Snake9.Component170
