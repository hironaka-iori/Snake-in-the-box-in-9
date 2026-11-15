import CutParity221

set_option Elab.async false

namespace EndpointParity225
open CutParity221

/-- The parity of coordinate changes is fixed by the two endpoint values.
This exposes the induction previously private in the accepted cycle module. -/
theorem path_change_parity (start finish : Bool) (middle : List Bool) :
    (changes start (middle ++ [finish])).count true % 2 =
      (if start = finish then 0 else 1) := by
  induction middle generalizing start finish with
  | nil => cases start <;> cases finish <;> simp [changes]
  | cons next tail ih =>
      have h := ih next finish
      cases start <;> cases finish <;> cases next <;>
        simp [changes, List.count_cons] at h ⊢ <;> omega

/-- Along any finite vertex walk, a Boolean coordinate changes its endpoint
disagreement plus an even number of times. In particular this applies to
the vertices of an actual replacement interval. -/
theorem coordinate_crossing_count {V : Type}
    (coordinate : V → Bool) (start finish : V) (middle : List V) :
    ∃ k : Nat,
      (changes (coordinate start) (middle.map coordinate ++ [coordinate finish])).count true =
        (if coordinate start = coordinate finish then 0 else 1) + 2 * k := by
  refine ⟨(changes (coordinate start)
    (middle.map coordinate ++ [coordinate finish])).count true / 2, ?_⟩
  have division := Nat.mod_add_div
    ((changes (coordinate start)
      (middle.map coordinate ++ [coordinate finish])).count true) 2
  rw [path_change_parity] at division
  exact division.symm

#print axioms path_change_parity
#print axioms coordinate_crossing_count
end EndpointParity225
