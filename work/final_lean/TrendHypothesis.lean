import Std

/- These are extrapolation models. They are not definitions of the true
   snake-in-the-box maximum, and no geometric optimality is assumed. -/
namespace SnakeTrend

def known : List Nat := [0, 1, 2, 4, 7, 13, 26, 50, 98]

def geometricTail (t : Nat) : Nat := 3 * 2 ^ t + 2 ^ (t / 3)

def geometricModel (n : Nat) : Nat :=
  if n < 3 then n else geometricTail (n - 3)

def linearModel (n : Nat) : Nat :=
  if n < 3 then n else 3 * 2 ^ (n - 3) + 1 + (n - 3) / 3

theorem geometric_matches_known : (List.range 9).map geometricModel = known := by decide
theorem linear_matches_known : (List.range 9).map linearModel = known := by decide

theorem correction_table :
    ((List.range 6).map (fun k => geometricModel (k+3) - 3 * 2^k)) =
      [1,1,1,2,2,2] := by decide

theorem geometric_prediction : geometricModel 9 = 196 := by decide
theorem linear_prediction : linearModel 9 = 195 := by decide

theorem first_eight_do_not_determine_ninth :
    ((List.range 9).map geometricModel = (List.range 9).map linearModel) ∧
    geometricModel 9 ≠ linearModel 9 := by decide

/- The general three-dimension recurrence of the proposed geometric model. -/
theorem geometricTail_step (t : Nat) :
    geometricTail (t + 3) + 6 * 2 ^ (t / 3) = 8 * geometricTail t := by
  have hd : (t + 3) / 3 = t / 3 + 1 := by omega
  simp only [geometricTail, hd, Nat.pow_add]
  simp only [show (2 : Nat)^3 = 8 from rfl, show (2 : Nat)^1 = 2 from rfl]
  omega

theorem ninth_from_recurrence : 8 * 26 - 6 * 2 = 196 := by decide

#print axioms geometric_matches_known
#print axioms geometric_prediction
#print axioms first_eight_do_not_determine_ninth
#print axioms geometricTail_step
end SnakeTrend
