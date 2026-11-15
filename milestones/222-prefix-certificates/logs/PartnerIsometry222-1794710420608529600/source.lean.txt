import Std

set_option Elab.async false

namespace PartnerIsometry222

/-- Pulling back a compatible induced partner through an adjacency-preserving
bijection preserves its length, designated joining index and avoidance of
every other parent index. The parent root index may be either endpoint. -/
theorem pullback_partner {V : Type} (Adj : V → V → Prop)
    (f g : V → V) (p q : Nat → V) (n m root : Nat)
    (left_inverse : ∀ v, g (f v) = v)
    (right_inverse : ∀ v, f (g v) = v)
    (adjacency : ∀ u v, Adj (f u) (f v) ↔ Adj u v)
    (q_distinct : ∀ i j, i ≤ m → j ≤ m → q i = q j → i = j)
    (q_induced : ∀ i j, i ≤ m → j ≤ m → i ≠ j →
      (Adj (q i) (q j) ↔ i + 1 = j ∨ j + 1 = i))
    (joining : q 0 = f (p root))
    (avoidance : ∀ i j, i ≤ m → j ≤ n → j ≠ root → q i ≠ f (p j)) :
    (∀ i j, i ≤ m → j ≤ m → g (q i) = g (q j) → i = j) ∧
    (∀ i j, i ≤ m → j ≤ m → i ≠ j →
      (Adj (g (q i)) (g (q j)) ↔ i + 1 = j ∨ j + 1 = i)) ∧
    g (q 0) = p root ∧
    (∀ i j, i ≤ m → j ≤ n → j ≠ root → g (q i) ≠ p j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hi hj equal
    have before : q i = q j := by
      have h := congrArg f equal
      simpa only [right_inverse] using h
    exact q_distinct i j hi hj before
  · intro i j hi hj different
    have transport : Adj (g (q i)) (g (q j)) ↔ Adj (q i) (q j) := by
      have h := (adjacency (g (q i)) (g (q j))).symm
      simpa only [right_inverse] using h
    exact transport.trans (q_induced i j hi hj different)
  · rw [joining, left_inverse]
  · intro i j hi hj different equal
    apply avoidance i j hi hj different
    have h := congrArg f equal
    simpa only [right_inverse] using h

#print axioms pullback_partner
end PartnerIsometry222
