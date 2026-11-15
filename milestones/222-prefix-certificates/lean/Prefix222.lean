import Std

set_option Elab.async false

namespace Prefix222

/-- Every next vertex of an actual induced path survives the elementary
prefix restrictions: allowed membership, the current edge, no repeated
prefix vertex, and no adjacency to an earlier prefix vertex. -/
theorem prefix_next {V : Type} (Adj : V → V → Prop) (allowed : V → Prop)
    (p : Nat → V) (n k : Nat)
    (membership : ∀ i, i ≤ n → allowed (p i))
    (distinct : ∀ i j, i ≤ n → j ≤ n → p i = p j → i = j)
    (induced : ∀ i j, i ≤ n → j ≤ n → i ≠ j →
      (Adj (p i) (p j) ↔ i + 1 = j ∨ j + 1 = i))
    (proper : k < n) :
    allowed (p (k + 1)) ∧ Adj (p k) (p (k + 1)) ∧
      (∀ i, i ≤ k → p (k + 1) ≠ p i) ∧
      (∀ i, i < k → ¬Adj (p i) (p (k + 1)) ∧
        ¬Adj (p (k + 1)) (p i)) := by
  have current_bound : k ≤ n := by omega
  have next_bound : k + 1 ≤ n := by omega
  refine ⟨membership (k + 1) next_bound, ?_, ?_, ?_⟩
  · exact (induced k (k + 1) current_bound next_bound (by omega)).mpr
      (Or.inl rfl)
  · intro i hi equal
    have equal_indices := distinct (k + 1) i next_bound (by omega) equal
    omega
  · intro i hi
    constructor
    · intro edge
      have consecutive := (induced i (k + 1) (by omega) next_bound
        (by omega)).mp edge
      omega
    · intro edge
      have consecutive := (induced (k + 1) i next_bound (by omega)
        (by omega)).mp edge
      omega

/-- A nonroot vertex of a proper prefix is neither full-path endpoint.
This includes the current last prefix vertex, which still has a next step. -/
theorem prefix_nonroot_not_endpoints {V : Type} (p : Nat → V) (n k i : Nat)
    (distinct : ∀ a b, a ≤ n → b ≤ n → p a = p b → a = b)
    (nonroot : 0 < i) (in_prefix : i ≤ k) (proper : k < n) :
    p i ≠ p 0 ∧ p i ≠ p n := by
  constructor
  · intro equal
    have equal_indices := distinct i 0 (by omega) (by omega) equal
    omega
  · intro equal
    have equal_indices := distinct i n (by omega) (by omega) equal
    omega

/-- The free-endpoint indicator of the full path vanishes at every
nonroot vertex of a proper prefix. No endpoint-value premise is used. -/
theorem prefix_free_endpoint_zero {V : Type} [DecidableEq V]
    (p : Nat → V) (n k i : Nat)
    (distinct : ∀ a b, a ≤ n → b ≤ n → p a = p b → a = b)
    (nonroot : 0 < i) (in_prefix : i ≤ k) (proper : k < n) :
    (if p i = p n then (1 : Int) else 0) = 0 := by
  have not_last := (prefix_nonroot_not_endpoints p n k i distinct
    nonroot in_prefix proper).2
  simp [not_last]

#print axioms prefix_next
#print axioms prefix_nonroot_not_endpoints
#print axioms prefix_free_endpoint_zero
end Prefix222
