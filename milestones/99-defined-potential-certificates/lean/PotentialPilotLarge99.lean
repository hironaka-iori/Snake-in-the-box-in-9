import PotentialPilot99
import PotentialChecker99

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Potential99
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78
open Snake9.PotentialChecker99 Snake9.DefinedGraph92 Snake9.Certificate88

theorem edgeTest_eq (floor : Nat → Nat) (P : Nat) (pi : Nat → Nat)
    (di q c : Nat) :
    edgeTest floor P pi di q c = edgeCheck (weight floor) P pi di q c := by
  simp only [edgeTest, edgeCheck, fastKeep_eq]
  cases h : diagramKeep retainedDiagram di q c <;> simp [h]

theorem completed_large_chunk :
    checkInterval (edgeTest completedCredit 483 Completed.potential 35 0)
      9720 2160 = true := by decide +kernel

theorem conditional_large_chunk :
    checkInterval (edgeTest conditionalCredit 496 Conditional.potential 177 43)
      9720 2160 = true := by decide +kernel

theorem completed_large_original :
    checkInterval (edgeCheck (weight completedCredit) 483 Completed.potential 35 0)
      9720 2160 = true := by
  simpa only [checkInterval, edgeTest_eq] using completed_large_chunk

theorem conditional_large_original :
    checkInterval (edgeCheck (weight conditionalCredit) 496 Conditional.potential 177 43)
      9720 2160 = true := by
  simpa only [checkInterval, edgeTest_eq] using conditional_large_chunk

#print axioms edgeTest_eq
#print axioms completed_large_chunk
#print axioms conditional_large_chunk
#print axioms completed_large_original
#print axioms conditional_large_original
end Snake9.Potential99
