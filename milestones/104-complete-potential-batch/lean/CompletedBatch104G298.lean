import BoundedPrefixTransfer102
import Context101Group05
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G298
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_42 (code%7776)) ≤
        120*(code%6+1)+max (max 7 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_146 (code/6)))) 6 0 3784 = true := by
  decide +kernel

theorem completed_context_217_2 :
    contextCheck (weight completedCredit) 483 Completed.potential 217 2 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_42 (code%7776)) ≤
        120*(code%6+1)+max (max 7 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_146 (code/6))))
    (weight completedCredit) 483 Completed.potential 217 2 92 block_217_2.1
  · simpa only [block_217_2.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_133 (code/6) (by omega)
    have ht := completed_at_11 (code%7776) (by omega)
    simp only [completed_217_2, source_217_2, target_217_2, hs, ht]

#print axioms completed_context_217_2

theorem completed_context_220_2 :
    contextCheck (weight completedCredit) 483 Completed.potential 220 2 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_42 (code%7776)) ≤
        120*(code%6+1)+max (max 7 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_146 (code/6))))
    (weight completedCredit) 483 Completed.potential 220 2 92 block_220_2.1
  · simpa only [block_220_2.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_133 (code/6) (by omega)
    have ht := completed_at_11 (code%7776) (by omega)
    simp only [completed_220_2, source_220_2, target_220_2, hs, ht]

#print axioms completed_context_220_2

#print axioms prefix_checked
end Snake9.CompletedBatch104G298
