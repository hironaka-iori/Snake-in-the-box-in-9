import LocalWindowSat.CycleWindow4905
import LocalWindowUnsat.CycleWindow4905
import LocalWindowBridge
namespace Snake9.LocalWindow.CycleWindow4905
theorem refuted : Refuted window bounds := Tags.refuted_of_sat sat unsat
def directions : List Nat := [0, 1, 2, 0, 3, 2]
theorem excluded_in_snake {m : Nat} (p : Snake m) (P : CPerm) (r : Nat)
    (hr : r + directions.length ≤ m)
    (hP : ∀ j, j < directions.length → P.fwd (dir p (r+j)) = directions.getD j 0)
    (hb : ∀ i, i < bounds.length →
      (bounds.getD i (0,21)).1 ≤ coreAlpha p (r+i+1) ∧
      coreAlpha p (r+i+1) ≤ (bounds.getD i (0,21)).2) : False :=
  refuted_bridge p P r (cs := directions) refuted ⟨rfl,rfl,by decide⟩ (by decide) hr hP hb
#print axioms refuted
#print axioms excluded_in_snake
end Snake9.LocalWindow.CycleWindow4905
