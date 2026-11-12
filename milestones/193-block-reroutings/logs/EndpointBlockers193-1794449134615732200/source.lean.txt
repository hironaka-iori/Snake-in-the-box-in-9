import Std
namespace EndpointBlockers193

/-- Every old blocker of an added endpoint lies in the replaced interior. -/
theorem blockerInterior {V : Type} (conflict : V → V → Prop)
    (p q : Nat → V) (w : V) (a b n e i : Nat)
    (outside : ∀ j, j ≤ a ∨ b ≤ j → q j = p j)
    (separate : ∀ j, j ≤ n → j ≠ e → ¬ conflict w (q j))
    (hi : i ≤ n) (hne : i ≠ e) (blocked : conflict w (p i)) :
    a < i ∧ i < b := by
  by_cases h : a < i ∧ i < b
  · exact h
  · have houtside : i ≤ a ∨ b ≤ i := by omega
    have hn := separate i hi hne
    rw [outside i houtside] at hn
    exact False.elim (hn blocked)

theorem requiredSpan (a b lo hi : Nat) (hlo : a < lo) (hhi : hi < b)
    (horder : lo ≤ hi) : hi-lo+2 ≤ b-a := by omega

#print axioms blockerInterior
#print axioms requiredSpan
end EndpointBlockers193
