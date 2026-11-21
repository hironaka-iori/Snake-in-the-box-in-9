import FreedSite250

namespace TwoTails252

open FreedSite250

variable {V : Type} {R : V → V → Prop} {w : Nat → V}

/-- Inducedness on the original indices of a suffix starting at a. -/
def InducedFrom (R : V → V → Prop) (w : Nat → V) (a n : Nat) : Prop :=
  ∀ i j, a ≤ i → i < j → j ≤ n →
    w i ≠ w j ∧ (R (w i) (w j) ↔ i + 1 = j)

/-- Cross contacts between the two portions strictly outside the retained segment. -/
def TailsSeparate (R : V → V → Prop) (w : Nat → V) (a b n : Nat) : Prop :=
  ∀ i j, i < a → b < j → j ≤ n → w i ≠ w j ∧ ¬ R (w i) (w j)

/-- Join two induced extensions of the same nonempty indexed segment [a,b].
The result also covers a singleton segment or an empty added portion. -/
theorem two_tails_iff {a b n : Nat} (hab : a ≤ b) (hbn : b ≤ n) :
    InducedThrough R w n ↔
      InducedThrough R w b ∧ InducedFrom R w a n ∧ TailsSeparate R w a b n := by
  constructor
  · intro whole
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij hj
      exact whole i j hij (by omega)
    · intro i j _ hij hj
      exact whole i j hij hj
    · intro i j hi hj hjn
      have pair := whole i j (by omega) hjn
      refine ⟨pair.1, ?_⟩
      intro edge
      have step := pair.2.mp edge
      omega
  · rintro ⟨left, right, separate⟩ i j hij hjn
    by_cases hleft : j ≤ b
    · exact left i j hij hleft
    · by_cases hright : a ≤ i
      · exact right i j hright hij hjn
      · have hi : i < a := by omega
        have hj : b < j := by omega
        have pair := separate i j hi hj hjn
        refine ⟨pair.1, ?_⟩
        constructor
        · intro edge
          exact (pair.2 edge).elim
        · intro step
          omega

#print axioms two_tails_iff

end TwoTails252
