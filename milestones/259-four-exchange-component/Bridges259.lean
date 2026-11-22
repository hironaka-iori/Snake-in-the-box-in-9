import Std.Tactic

namespace Bridges259

/-- An exchange chain on the three components obtained with at most three replacements.
The last index counts four-replacement steps. The finite enumeration supplies the
two conditions: smaller steps stay inside a component and a four-step moves its
index by at most one in either direction. -/
inductive Chain : Nat → Nat → Nat → Prop
  | nil (a) : Chain a a 0
  | small {a b k} : Chain a b k → Chain a b k
  | four {a b c k} : Chain a b k → c ≤ b + 1 → b ≤ c + 1 → Chain a c (k+1)

theorem displacement {a b k : Nat} (h : Chain a b k) :
    b ≤ a + k ∧ a ≤ b + k := by
  induction h with
  | nil => omega
  | small _ ih => exact ih
  | four _ _ _ ih => obtain ⟨_, _⟩ := ih; constructor <;> omega

theorem far_group_requires_two {k : Nat} (h : Chain 0 2 k) : 2 ≤ k := by
  have bound := (displacement h).1
  omega

theorem two_suffice_on_quotient : Chain 0 2 2 := by
  have first : Chain 0 1 1 := .four (.nil 0) (by decide) (by decide)
  exact .four first (by decide) (by decide)

end Bridges259

#print axioms Bridges259.displacement
#print axioms Bridges259.far_group_requires_two
#print axioms Bridges259.two_suffice_on_quotient
