import PrefixChecker100
import CompletedPotential99

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.PrefixCertificates100
open Snake9.PrefixChecker100 Snake9.PotentialChecker99 Snake9.Potential99
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92

theorem completed_prefix :
    checkPrefix (fun code => decide
      (483+Completed.potential (edgeTarget 0 35 code) ≤
        weight completedCredit 0 35 code+Completed.potential (edgeSource 0 35 code)))
      6 0 2620 = true := by decide +kernel

theorem completed_context :
    contextCheck (weight completedCredit) 483 Completed.potential 35 0 = true := by
  apply contextCheck_of_prefix (weight completedCredit) 483 Completed.potential 35 0 25
  · decide +kernel
  · exact completed_prefix

#print axioms completed_prefix
#print axioms completed_context
end Snake9.PrefixCertificates100
