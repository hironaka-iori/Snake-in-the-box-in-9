import LayerJoining

set_option Elab.async false

namespace ReplacementConditions225
open LayerJoining

/-- Internal packaging of the existing local replacement premises.
No global injectivity or inducedness of q is a field. -/
structure Conditions {V : Type} {R : V → V → Prop} {n : Nat}
    (p : InducedPath V R n) (q : Fin (n + 1) → V) (a b c d : Nat) : Prop where
  ordered : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ n
  agreement : ∀ i, ¬(a < i.val ∧ i.val < b) →
    ¬(c < i.val ∧ i.val < d) → q i = p.vertex i
  first_distinct : ∀ i j, a ≤ i.val → i.val ≤ b →
    a ≤ j.val → j.val ≤ b → q i = q j → i = j
  first_induced : ∀ i j, a ≤ i.val → j.val ≤ b → i.val < j.val →
    (R (q i) (q j) ↔ i.val + 1 = j.val)
  second_distinct : ∀ i j, c ≤ i.val → i.val ≤ d →
    c ≤ j.val → j.val ≤ d → q i = q j → i = j
  second_induced : ∀ i j, c ≤ i.val → j.val ≤ d → i.val < j.val →
    (R (q i) (q j) ↔ i.val + 1 = j.val)
  first_separated : ∀ i j, (a < i.val ∧ i.val < b) →
    ¬(c < j.val ∧ j.val < d) → (j.val < a ∨ b < j.val) →
    q i ≠ p.vertex j ∧ ¬R (q i) (p.vertex j) ∧ ¬R (p.vertex j) (q i)
  second_separated : ∀ i j, (c < i.val ∧ i.val < d) →
    ¬(a < j.val ∧ j.val < b) → (j.val < c ∨ d < j.val) →
    q i ≠ p.vertex j ∧ ¬R (q i) (p.vertex j) ∧ ¬R (p.vertex j) (q i)
  mutual : ∀ i j, (a < i.val ∧ i.val < b) →
    (c < j.val ∧ j.val < d) → q i ≠ q j ∧ ¬R (q i) (q j)

#print axioms Conditions.mk
end ReplacementConditions225
