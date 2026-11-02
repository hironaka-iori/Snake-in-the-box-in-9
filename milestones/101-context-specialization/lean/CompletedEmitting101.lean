import PrefixChecker100
import EmittingReduction101
import CompletedPotential99

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.PrefixCertificates101
open Snake9.PrefixChecker100 Snake9.PotentialChecker99 Snake9.Potential99
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.Context101 Snake9.ConcreteCatalogue95
open Snake9.Guards79

theorem completed_prefix_99_37 :
    checkPrefix (fun code => decide
      (483+Completed.potential (1080864+code%7776) ≤
        120*(code%6+1)+max (if digit code 1 ≤ 2 ∧ digit code 2 ≤ 2 then 19 else 18) (if code%7776 = 3221 then 96 else 0)+Completed.potential (1306368+code/6)))
      6 0 1807 = true := by decide +kernel

theorem completed_context_99_37 :
    contextCheck (weight completedCredit) 483 Completed.potential 99 37 = true := by
  apply contextCheck_of_prefix (weight completedCredit) 483 Completed.potential 99 37 12
  · exact block_99_37.1
  · rw [block_99_37.2]
    simpa only [completed_simplified_99_37, source_99_37, target_99_37]
      using completed_prefix_99_37

#print axioms completed_prefix_99_37
#print axioms completed_context_99_37
end Snake9.PrefixCertificates101
