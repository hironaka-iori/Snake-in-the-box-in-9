import AlternatingCounts191

set_option Elab.async false

namespace FixedColour232
open Replacement191

/-- The number of edges of an alternating sequence is at most twice
the number of vertices of either chosen colour. -/
theorem length_le_twice_colour (L n : Nat) (f : Nat → Nat)
    (alternating : ∀ i, i + 1 < L + 1 → f i + f (i + 1) = 1)
    (count : colourSum f (L + 1) = n) : L ≤ 2 * n := by
  let k : Nat := (L + 1) / 2
  have pairs : colourSum f (2 * k) = k := by
    apply pairedCount
    intro i hi
    apply alternating (2 * i)
    dsimp [k] at hi
    omega
  have hcases : L + 1 = 2 * k ∨ L + 1 = 2 * k + 1 := by
    dsimp [k]
    omega
  rcases hcases with even | odd
  · rw [even, pairs] at count
    omega
  · rw [odd] at count
    change colourSum f (2 * k) + f (2 * k) = n at count
    rw [pairs] at count
    omega

/-- Excluding the unique largest possible length makes the bound strict. -/
theorem strict_length_bound (L n : Nat) (f : Nat → Nat)
    (alternating : ∀ i, i + 1 < L + 1 → f i + f (i + 1) = 1)
    (count : colourSum f (L + 1) = n) (excluded : L ≠ 2 * n) :
    L + 1 ≤ 2 * n := by
  have bound := length_le_twice_colour L n f alternating count
  omega

/-- With exactly 96 vertices of a chosen colour, a separate exclusion
of length 192 gives length at most 191. -/
theorem fixed_96_bound (L : Nat) (f : Nat → Nat)
    (alternating : ∀ i, i + 1 < L + 1 → f i + f (i + 1) = 1)
    (count : colourSum f (L + 1) = 96) (excluded : L ≠ 192) :
    L ≤ 191 := by
  have bound := strict_length_bound L 96 f alternating count (by simpa using excluded)
  omega

#print axioms length_le_twice_colour
#print axioms strict_length_bound
#print axioms fixed_96_bound

end FixedColour232
