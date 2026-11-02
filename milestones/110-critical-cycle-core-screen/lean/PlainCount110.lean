import Recovered110.LocalWindowSat.D012340A55245
import Recovered110.LocalWindowUnsat.D012340A55245
import ReferenceInterface

namespace Snake9.CriticalCount110
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.GraphInterpretation75 Snake9.GraphWalk78 Snake9.CountGeometry78
open Snake9.Guards79 Snake9.Reference85
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem count_pattern_refuted :
    Refuted (winOf [0,1,2,3,4,0]) (boundsOf [5,5,2,4,5]) :=
  Tags.refuted_of_sat D012340A55245.sat D012340A55245.unsat

theorem actual_counts_excluded {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,3,4,0]) :
    ¬ (coreAlpha p (r+1) = 5 ∧ coreAlpha p (r+2) = 5 ∧
      coreAlpha p (r+3) = 2 ∧ coreAlpha p (r+4) = 4 ∧
      coreAlpha p (r+5) = 5) := by
  rintro ⟨h₁,h₂,h₃,h₄,h₅⟩
  apply canonical_interval_exclusion p r 6 [0,1,2,3,4,0]
    (boundsOf [5,5,2,4,5]) hr rfl hshape count_pattern_refuted
  intro i hi
  change i < 5 at hi
  interval_cases i <;> simp_all [boundsOf, boundOf]

theorem actual_graph_exclusion {m : Nat} (p : Snake m) (r s : Nat)
    (hr : r+9 ≤ m) (hs : s ≤ 1) :
    ¬ forwardHit p r s ([0,1,2,3,4,0],[5,5,2,4,5]) ∧
    ¬ reverseHit p r s ([0,1,2,3,4,0],[5,5,2,4,5]) := by
  apply refuted_key_retained p r s _ hr (by simpa using Nat.add_le_add_right hs 5)
    (by decide +kernel) count_pattern_refuted

#print axioms count_pattern_refuted
#print axioms actual_counts_excluded
#print axioms actual_graph_exclusion
#print axioms Snake9.LocalWindow.D012340A55245.check
#print axioms Snake9.LocalWindow.D012340A55245.sat
#print axioms Snake9.LocalWindow.D012340A55245.unsat
end Snake9.CriticalCount110
