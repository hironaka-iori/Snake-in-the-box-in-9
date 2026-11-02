import DirectionTables
import ExactHistory
namespace Snake9.Direction77
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def recordedCompatible : List Nat := [0, 62, 63, 66, 101, 87, 119, 42, 44, 101, 124, 15, 16, 23, 10, 23, 101, 110, 124, 25, 28, 52, 49, 51, 52, 124, 81, 88, 101, 101, 110, 124, 23, 10, 23, 52, 49, 28, 88, 87, 101, 124, 52, 51, 101, 78, 87, 88, 124, 100, 101, 124, 52, 52, 124, 101, 42, 44, 21, 22, 10, 11, 16, 21, 22, 101, 124, 25, 52, 50, 51, 52, 51, 124, 101]
def compatibleShape (q : Nat) : Nat :=
  targetId ((Snake9.History75.prefixes.getD q []).getLastD 0)
def compatibilityCheck (q : Nat) : Bool :=
  q == 0 || (recordedCompatible.getD q 0 == compatibleShape q)
theorem compatibility_checked : allBelow 75 compatibilityCheck = true := by
  decide +kernel
theorem recorded_compatible_exact (q : Nat) (h0 : q ≠ 0) (hq : q < 75) :
    recordedCompatible.getD q 0 = compatibleShape q := by
  have h := allBelow_spec 75 _ compatibility_checked q hq
  simpa [compatibilityCheck, h0] using h
#print axioms compatibility_checked
#print axioms recorded_compatible_exact
end Snake9.Direction77
