/-
Parametric lumped count `symK K a = min a K`, for automata whose symbols are the exact
counts 1..K-1 and "at least K" (the shared `sym` is the case K = 6).  Core Lean only.
-/
namespace Snake9.WindowAutomaton

def symK (K a : Nat) : Nat := min a K

theorem symK_le (K a : Nat) : symK K a ≤ a := Nat.min_le_left a K

theorem symK_le_K (K a : Nat) : symK K a ≤ K := Nat.min_le_right a K

theorem symK_ge_one (K a : Nat) (hK : 1 ≤ K) (h : 1 ≤ a) : 1 ≤ symK K a := Nat.le_min.mpr ⟨h, hK⟩

end Snake9.WindowAutomaton
