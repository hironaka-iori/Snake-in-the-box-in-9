import BoundedPrefixTransfer102
import Context101Group09
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G489
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_171 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_67 (code/6)))) 6 0 2231 = true := by
  decide +kernel

theorem completed_context_357_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 357 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_171 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_67 (code/6))))
    (weight completedCredit) 483 Completed.potential 357 0 17 block_357_0.1
  · simpa only [block_357_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_102 (code/6) (by omega)
    have ht := completed_at_64 (code%7776) (by omega)
    simp only [completed_357_0, source_357_0, target_357_0, hs, ht]

#print axioms completed_context_357_0

theorem completed_context_375_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 375 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_171 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_67 (code/6))))
    (weight completedCredit) 483 Completed.potential 375 0 17 block_375_0.1
  · simpa only [block_375_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_106 (code/6) (by omega)
    have ht := completed_at_64 (code%7776) (by omega)
    simp only [completed_375_0, source_375_0, target_375_0, hs, ht]

#print axioms completed_context_375_0

#print axioms prefix_checked
end Snake9.CompletedBatch104G489
