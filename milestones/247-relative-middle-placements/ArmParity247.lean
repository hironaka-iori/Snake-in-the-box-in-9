import Std

namespace ArmParity247

/-- Count the requested colour along an alternating arm of `a` edges, including both ends. -/
def colourCount : Nat → Bool → Bool → Nat
  | 0, start, wanted => if start = wanted then 1 else 0
  | a + 1, start, wanted =>
    (if start = wanted then 1 else 0) + colourCount a (!start) wanted

theorem colour_counts (a : Nat) (start : Bool) :
    colourCount a start start = (a + 2) / 2 ∧
    colourCount a start (!start) = (a + 1) / 2 := by
  induction a generalizing start with
  | zero => cases start <;> decide
  | succ a ih =>
    have ht := ih true
    have hf := ih false
    cases start <;> constructor <;> simp [colourCount] at ht hf ⊢ <;> omega

/-- The total quota before the model subtracts its already selected vertices. -/
theorem colour_quota (a : Nat) (start wanted : Bool) :
    colourCount a start wanted =
      (a + 1) / 2 + (if a % 2 = 0 ∧ wanted = start then 1 else 0) := by
  obtain ⟨same, other⟩ := colour_counts a start
  by_cases h : wanted = start
  · subst wanted
    rw [same]
    by_cases even : a % 2 = 0 <;> simp [even] <;> omega
  · have opposite : wanted = !start := by
      cases start <;> cases wanted <;> simp_all
    have noExtra : ¬ (a % 2 = 0 ∧ wanted = start) := fun pair => h pair.2
    rw [if_neg noExtra, Nat.add_zero, opposite, other]

def endColour : Nat → Bool → Bool
  | 0, start => start
  | a + 1, start => endColour a (!start)

theorem endColour_by_parity (a : Nat) (start : Bool) :
    endColour a start = (if a % 2 = 0 then start else !start) := by
  induction a generalizing start with
  | zero => simp [endColour]
  | succ a ih =>
    rw [endColour, ih]
    by_cases h : a % 2 = 0
    · have hnext : (a + 1) % 2 ≠ 0 := by omega
      simp [h, hnext]
    · have hnext : (a + 1) % 2 = 0 := by omega
      simp [h, hnext]

#print axioms colour_counts
#print axioms colour_quota
#print axioms endColour_by_parity

end ArmParity247
