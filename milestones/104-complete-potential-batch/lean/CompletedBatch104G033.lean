import BoundedPrefixTransfer102
import Context101Group00
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G033
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_73 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_51 (code/6)))) 6 0 2620 = true := by
  decide +kernel

theorem completed_context_34_14 :
    contextCheck (weight completedCredit) 483 Completed.potential 34 14 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_73 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_51 (code/6))))
    (weight completedCredit) 483 Completed.potential 34 14 25 block_34_14.1
  · simpa only [block_34_14.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_145 (code/6) (by omega)
    have ht := completed_at_180 (code%7776) (by omega)
    simp only [completed_34_14, source_34_14, target_34_14, hs, ht]

#print axioms completed_context_34_14

theorem completed_context_35_14 :
    contextCheck (weight completedCredit) 483 Completed.potential 35 14 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_73 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_51 (code/6))))
    (weight completedCredit) 483 Completed.potential 35 14 25 block_35_14.1
  · simpa only [block_35_14.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_145 (code/6) (by omega)
    have ht := completed_at_181 (code%7776) (by omega)
    simp only [completed_35_14, source_35_14, target_35_14, hs, ht]

#print axioms completed_context_35_14

#print axioms prefix_checked
end Snake9.CompletedBatch104G033
