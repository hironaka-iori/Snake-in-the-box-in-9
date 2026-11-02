import PotentialPilotLarge99

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Potential99
open Snake9.Weights98 Snake9.CountFree98 Snake9.PotentialChecker99

theorem completed_context_fast :
    checkInterval (edgeTest completedCredit 483 Completed.potential 35 0)
      0 46656 = true := by decide +kernel

theorem completed_context :
    contextCheck (weight completedCredit) 483 Completed.potential 35 0 = true := by
  simpa only [contextCheck, checkInterval, edgeTest_eq] using completed_context_fast

#print axioms completed_context_fast
#print axioms completed_context
end Snake9.Potential99
