import PrefixChecker100
import ConditionalPotential99

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.PrefixCertificates100
open Snake9.PrefixChecker100 Snake9.PotentialChecker99 Snake9.Potential99
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92

theorem conditional_prefix :
    checkPrefix (fun code => decide
      (496+Conditional.potential (edgeTarget 43 177 code) ≤
        weight conditionalCredit 43 177 code+Conditional.potential (edgeSource 43 177 code)))
      6 0 3690 = true := by decide +kernel

theorem conditional_context :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 177 43 = true := by
  apply contextCheck_of_prefix (weight conditionalCredit) 496 Conditional.potential 177 43 85
  · decide +kernel
  · exact conditional_prefix

#print axioms conditional_prefix
#print axioms conditional_context
end Snake9.PrefixCertificates100
