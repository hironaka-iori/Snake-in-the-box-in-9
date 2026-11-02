import PrefixChecker100
import WeightSpecialization100
import ContextEndpoints100
import CompletedPotential99

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.PrefixCertificates100
open Snake9.PrefixChecker100 Snake9.PotentialChecker99 Snake9.Potential99
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.WeightSpecialization100 Snake9.ContextEndpoints100

theorem completed_prefix_reduced :
    checkPrefix (fun code => decide
      (483+Completed.potential (1049760+code%7776) ≤
        120*(code%6+1)+(if code%7776=7106 then 96 else 0)+
          Completed.potential (77760+code/6))) 6 0 2620 = true := by
  decide +kernel

theorem completed_context_reduced :
    contextCheck (weight completedCredit) 483 Completed.potential 35 0 = true := by
  apply contextCheck_of_prefix (weight completedCredit) 483 Completed.potential 35 0 25
  · decide +kernel
  · change checkPrefix (fun code => decide
        (483+Completed.potential (edgeTarget 0 35 code) ≤
          weight completedCredit 0 35 code+Completed.potential (edgeSource 0 35 code)))
        6 0 2620 = true
    simpa only [completed_weight_direction35, source35, target35]
      using completed_prefix_reduced

#print axioms completed_prefix_reduced
#print axioms completed_context_reduced
end Snake9.PrefixCertificates100
