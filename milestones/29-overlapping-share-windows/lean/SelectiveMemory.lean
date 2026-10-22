import Mathlib.Tactic

namespace Snake9.SelectiveMemory

/-- History is stored most-recent entry first. -/
def leadingFours : List Nat → Nat
  | [] => 0
  | a :: xs => if a = 4 then leadingFours xs + 1 else 0

def state (xs : List Nat) : Nat := min 6 (leadingFours xs)

theorem update (xs : List Nat) (a : Nat) :
    state (a :: xs) = if a = 4 then min 6 (state xs + 1) else 0 := by
  by_cases h : a = 4
  · simp only [state, leadingFours, h, if_true]
    omega
  · simp [state, leadingFours, h]

theorem prefix_characterization (n : Nat) (xs : List Nat) :
    n ≤ leadingFours xs ↔ xs.take n = List.replicate n 4 := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => simp [leadingFours]
    | cons a xs =>
      by_cases h : a = 4
      · subst a
        simpa [leadingFours, List.replicate_succ] using ih xs
      · simp [leadingFours, h, List.replicate_succ]

theorem trigger (xs : List Nat) (a : Nat) :
    (state xs = 6 ∧ a = 4) ↔ (a :: xs).take 7 = List.replicate 7 4 := by
  rw [← prefix_characterization]
  by_cases h : a = 4
  · simp only [state, leadingFours, h, if_true, and_true]
    omega
  · simp [leadingFours, h]

theorem state_count : 34 * (6^4 + 2) = 44132 := by decide

#print axioms update
#print axioms prefix_characterization
#print axioms trigger
#print axioms state_count
end Snake9.SelectiveMemory
