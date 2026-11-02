import PotentialPilotLarge99

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Potential99
open Snake9.Weights98 Snake9.CountFree98 Snake9.PotentialChecker99

theorem conditional_context_fast :
    checkInterval (edgeTest conditionalCredit 496 Conditional.potential 177 43)
      0 46656 = true := by decide +kernel

theorem conditional_context :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 177 43 = true := by
  simpa only [contextCheck, checkInterval, edgeTest_eq] using conditional_context_fast

#print axioms conditional_context_fast
#print axioms conditional_context
end Snake9.Potential99
