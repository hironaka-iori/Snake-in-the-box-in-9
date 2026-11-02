import PotentialTree99

/-! One guarded base-six step in an existing potential tree. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Snake9.Joint103
open Snake9.Potential99

/-- Constant leaves remain valid at every depth. Internal nodes require
the expected interval width and a zero-based digit from zero through five. -/
def step (width digit : Nat) : Tree → Option Tree
  | .leaf n => some (.leaf n)
  | .node stored a b c d e f =>
      if stored = width then
        match digit with
        | 0 => some a
        | 1 => some b
        | 2 => some c
        | 3 => some d
        | 4 => some e
        | 5 => some f
        | _ => none
      else none

theorem step_value (tree child : Tree) (width digit offset : Nat)
    (hd : digit < 6) (hoff : offset < width)
    (hs : step width digit tree = some child) :
    value tree (digit*width+offset) = value child offset := by
  cases tree with
  | leaf n =>
      have hc : Tree.leaf n = child := Option.some.inj hs
      subst child
      rfl
  | node stored a b c d e f =>
      by_cases hw : stored = width
      · subst stored
        have hcases : digit = 0 ∨ digit = 1 ∨ digit = 2 ∨
            digit = 3 ∨ digit = 4 ∨ digit = 5 := by omega
        rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals
          simp only [step, if_pos rfl] at hs
          have hc := Option.some.inj hs
          subst child
          simp only [value]
          split_ifs <;> try omega
        all_goals
          congr 1
          omega
      · simp [step, hw] at hs

#print axioms step_value
end Snake9.Joint103
