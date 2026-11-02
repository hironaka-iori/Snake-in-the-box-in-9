import JointTraversal103
import BoundedPrefixTransfer102
import Context101Group00
import PotentialRoots102Group00

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Baseline103
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem completed_prefix_0_0 :
    checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_36 (code%7776)) ≤
        120*(code%6+1)+max (max 7 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_5 (code/6)))) 6 0 185 = true := by decide +kernel

theorem completed_context_0_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 0 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_36 (code%7776)) ≤
        120*(code%6+1)+max (max 7 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_5 (code/6))))
    (weight completedCredit) 483 Completed.potential 0 0 0 block_0_0.1
  · simpa only [block_0_0.2] using completed_prefix_0_0
  · intro code hc _
    have hs := completed_at_0 (code/6) (by omega)
    have ht := completed_at_29 (code%7776) (by omega)
    simp only [completed_0_0, source_0_0, target_0_0, hs, ht]

#print axioms completed_prefix_0_0
#print axioms completed_context_0_0
end Snake9.Baseline103
