import BoundedPrefixTransfer102
import Context101Group10
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G544
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_3 (code%7776)) ≤
        120*(code%6+1)+max (max 6 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_125 (code/6)))) 6 0 3982 = true := by
  decide +kernel

theorem completed_context_438_6 :
    contextCheck (weight completedCredit) 483 Completed.potential 438 6 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_3 (code%7776)) ≤
        120*(code%6+1)+max (max 6 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_125 (code/6))))
    (weight completedCredit) 483 Completed.potential 438 6 126 block_438_6.1
  · simpa only [block_438_6.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_137 (code/6) (by omega)
    have ht := completed_at_169 (code%7776) (by omega)
    simp only [completed_438_6, source_438_6, target_438_6, hs, ht]

#print axioms completed_context_438_6

theorem completed_context_439_6 :
    contextCheck (weight completedCredit) 483 Completed.potential 439 6 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_3 (code%7776)) ≤
        120*(code%6+1)+max (max 6 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_125 (code/6))))
    (weight completedCredit) 483 Completed.potential 439 6 126 block_439_6.1
  · simpa only [block_439_6.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_137 (code/6) (by omega)
    have ht := completed_at_170 (code%7776) (by omega)
    simp only [completed_439_6, source_439_6, target_439_6, hs, ht]

#print axioms completed_context_439_6

#print axioms prefix_checked
end Snake9.CompletedBatch104G544
