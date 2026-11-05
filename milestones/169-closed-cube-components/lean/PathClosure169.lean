import PathStructure

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Snake9.PathClosure169

-- Only the intersection of A with the selected path matters. No finite-set
-- representation or global assumption A subset InPath is required.
theorem closed_selected_contains_all {m : Nat} (p : Snake m)
    (A : Vertex → Prop)
    (nonempty : ∃ v, InPath p v ∧ A v)
    (closed : ∀ u v, InPath p u → A u → InPath p v → Adj u v → A v) :
    ∀ v, InPath p v → A v := by
  have reach_zero : ∀ n, (hn : n < m + 1) →
      A (p.vertex ⟨n, hn⟩) → A (p.vertex ⟨0, by omega⟩) := by
    intro n
    induction n with
    | zero =>
      intro hn hA
      exact hA
    | succ n ih =>
      intro hn hA
      have hn' : n < m + 1 := by omega
      apply ih hn'
      apply closed (p.vertex ⟨n + 1, hn⟩) (p.vertex ⟨n, hn'⟩)
        ⟨⟨n + 1, hn⟩, rfl⟩ hA ⟨⟨n, hn'⟩, rfl⟩
      apply (path_adj_iff p _ _).mpr
      exact Or.inr rfl
  obtain ⟨v, ⟨i, hi⟩, hA⟩ := nonempty
  have hstart : A (p.vertex ⟨0, by omega⟩) :=
    reach_zero i.val i.isLt (by simpa only [hi] using hA)
  have reach_all : ∀ n, (hn : n < m + 1) → A (p.vertex ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact hstart
    | succ n ih =>
      intro hn
      have hn' : n < m + 1 := by omega
      apply closed (p.vertex ⟨n, hn'⟩) (p.vertex ⟨n + 1, hn⟩)
        ⟨⟨n, hn'⟩, rfl⟩ (ih hn') ⟨⟨n + 1, hn⟩, rfl⟩
      apply (path_adj_iff p _ _).mpr
      exact Or.inl rfl
  intro w hw
  obtain ⟨j, rfl⟩ := hw
  exact reach_all j.val j.isLt

theorem closed_selected_no_outside {m : Nat} (p : Snake m)
    (A : Vertex → Prop)
    (nonempty : ∃ v, InPath p v ∧ A v)
    (closed : ∀ u v, InPath p u → A u → InPath p v → Adj u v → A v)
    (outside : ∃ v, InPath p v ∧ ¬ A v) : False := by
  obtain ⟨v, hv, hn⟩ := outside
  exact hn (closed_selected_contains_all p A nonempty closed v hv)

#print axioms closed_selected_contains_all
#print axioms closed_selected_no_outside

end Snake9.PathClosure169
