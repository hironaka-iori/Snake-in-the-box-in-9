import BoundedPrefixTransfer102
import Context101Group00
import PotentialRoots102Group00

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.PrefixCertificates102
open Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem completed_prefix_1_0 :
    checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_81 (code%7776)) ≤
        120*(code%6+1)+max (max 11 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_5 (code/6)))) 6 0 379 = true := by decide +kernel

theorem completed_context_1_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 1 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_81 (code%7776)) ≤
        120*(code%6+1)+max (max 11 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_5 (code/6))))
    (weight completedCredit) 483 Completed.potential 1 0 1 block_1_0.1
  · simpa only [block_1_0.2] using completed_prefix_1_0
  · intro code hc _
    have hs := completed_at_0 (code/6) (by omega)
    have ht := completed_at_30 (code%7776) (by omega)
    simp only [completed_1_0, source_1_0, target_1_0, hs, ht]

#print axioms completed_prefix_1_0
#print axioms completed_context_1_0
end Snake9.PrefixCertificates102
