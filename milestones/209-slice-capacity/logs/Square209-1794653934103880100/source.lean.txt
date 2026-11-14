import Std

namespace Square209

abbrev Vertex := Bool × Bool

def distance (a b : Vertex) : Nat :=
  (if a.1 = b.1 then 0 else 1) + (if a.2 = b.2 then 0 else 1)

def opposite (a : Vertex) : Vertex := (!a.1, !a.2)

theorem far_iff_opposite (a b : Vertex) :
    2 ≤ distance a b ↔ a = opposite b := by
  rcases a with ⟨a₀, a₁⟩
  rcases b with ⟨b₀, b₁⟩
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;>
    decide

theorem opposite_involutive (a : Vertex) : opposite (opposite a) = a := by
  rcases a with ⟨a₀, a₁⟩
  cases a₀ <;> cases a₁ <;> rfl

/-- Nonempty visit lists with every cross pair far apart are singleton sets
at opposite square vertices. Lists may contain repeated entries. -/
theorem far_visit_sets (s t : List Vertex) (a b : Vertex)
    (ha : a ∈ s) (hb : b ∈ t)
    (hfar : ∀ x, x ∈ s → ∀ y, y ∈ t → 2 ≤ distance x y) :
    (∀ x, x ∈ s → x = a) ∧
    (∀ y, y ∈ t → y = b) ∧ a = opposite b := by
  have hab : a = opposite b := (far_iff_opposite a b).mp (hfar a ha b hb)
  refine ⟨?_, ?_, hab⟩
  · intro x hx
    exact ((far_iff_opposite x b).mp (hfar x hx b hb)).trans hab.symm
  · intro y hy
    have hay : a = opposite y := (far_iff_opposite a y).mp (hfar a ha y hy)
    have heq : opposite y = opposite b := hay.symm.trans hab
    have h := congrArg opposite heq
    simpa only [opposite_involutive] using h

/-- A shared free word reduces a separated cross pair to its base distance. -/
theorem equal_free_word_separation (base free : Nat)
    (hfree : free = 0) (hsep : 2 ≤ base + free) : 2 ≤ base := by
  simpa [hfree] using hsep

#print axioms far_iff_opposite
#print axioms opposite_involutive
#print axioms far_visit_sets
#print axioms equal_free_word_separation

end Square209
