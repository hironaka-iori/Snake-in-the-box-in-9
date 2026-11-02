import BoundedPrefixTransfer102
import Context101Group02
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G125
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_80 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_15 (code/6)))) 6 0 2004 = true := by
  decide +kernel

theorem completed_context_98_20 :
    contextCheck (weight completedCredit) 483 Completed.potential 98 20 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_80 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_15 (code/6))))
    (weight completedCredit) 483 Completed.potential 98 20 14 block_98_20.1
  · simpa only [block_98_20.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_151 (code/6) (by omega)
    have ht := completed_at_47 (code%7776) (by omega)
    simp only [completed_98_20, source_98_20, target_98_20, hs, ht]

#print axioms completed_context_98_20

#print axioms prefix_checked
end Snake9.CompletedBatch104G125
