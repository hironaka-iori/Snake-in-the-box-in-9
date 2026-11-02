import BoundedPrefixTransfer102
import Context101Group11
import JointTraversal103
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G552
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_27 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_29 (code/6)))) 6 0 3934 = true := by
  decide +kernel

theorem completed_context_453_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 453 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_27 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_29 (code/6))))
    (weight completedCredit) 483 Completed.potential 453 0 118 block_453_0.1
  · simpa only [block_453_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_122 (code/6) (by omega)
    have ht := completed_at_105 (code%7776) (by omega)
    simp only [completed_453_0, source_453_0, target_453_0, hs, ht]

#print axioms completed_context_453_0

theorem completed_context_467_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 467 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_27 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_29 (code/6))))
    (weight completedCredit) 483 Completed.potential 467 0 118 block_467_0.1
  · simpa only [block_467_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_125 (code/6) (by omega)
    have ht := completed_at_105 (code%7776) (by omega)
    simp only [completed_467_0, source_467_0, target_467_0, hs, ht]

#print axioms completed_context_467_0

#print axioms prefix_checked
end Snake9.CompletedBatch104G552
