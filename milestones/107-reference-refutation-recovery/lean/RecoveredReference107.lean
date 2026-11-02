import Recovered107.LocalWindowSat.Q012A11
import Recovered107.LocalWindowUnsat.Q012A11
import ReferenceUnion

namespace Snake9.RecoveredReference107
open Snake9.LocalWindow Snake9.Reference85
set_option maxHeartbeats 2000000

theorem adjacent_ones_refuted : Refuted (winOf [0, 1, 2]) (boundsOf [1, 1]) :=
  Tags.refuted_of_sat Q012A11.sat Q012A11.unsat

theorem first_reference_key :
    referenceKeys.head? = some ([0, 1, 2], [1, 1]) := by decide +kernel

theorem reference_union_iff_remaining :
    AllRefutedList referenceKeys ↔ AllRefutedList referenceKeys.tail := by
  change (Refuted (winOf [0, 1, 2]) (boundsOf [1, 1]) ∧
    AllRefutedList referenceKeys.tail) ↔ AllRefutedList referenceKeys.tail
  exact ⟨And.right, fun h => ⟨adjacent_ones_refuted, h⟩⟩

theorem remaining_key_count : referenceKeys.tail.length = 1377 := by decide +kernel

#print axioms adjacent_ones_refuted
#print axioms first_reference_key
#print axioms reference_union_iff_remaining
#print axioms remaining_key_count
#print axioms Snake9.LocalWindow.Q012A11.check
#print axioms Snake9.LocalWindow.Q012A11.sat
#print axioms Snake9.LocalWindow.Q012A11.unsat
#print axioms Snake9.LocalWindow.Q012A11.ok1
#print axioms Snake9.LocalWindow.Q012A11.ok2
#print axioms Snake9.LocalWindow.Q012A11.ok3
#print axioms Snake9.LocalWindow.Q012A11.ok4
#print axioms Snake9.LocalWindow.Q012A11.ok5
#print axioms Snake9.LocalWindow.Q012A11.ok6
#print axioms Snake9.LocalWindow.Q012A11.ok7
end Snake9.RecoveredReference107
