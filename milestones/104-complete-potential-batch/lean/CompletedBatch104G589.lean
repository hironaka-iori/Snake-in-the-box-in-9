import BoundedPrefixTransfer102
import Context101Group12
import JointTraversal103
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G589
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_29 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_54 (code/6)))) 6 0 3906 = true := by
  decide +kernel

theorem completed_context_493_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 493 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_29 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_54 (code/6))))
    (weight completedCredit) 483 Completed.potential 493 0 113 block_493_0.1
  · simpa only [block_493_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_130 (code/6) (by omega)
    have ht := completed_at_125 (code%7776) (by omega)
    simp only [completed_493_0, source_493_0, target_493_0, hs, ht]

#print axioms completed_context_493_0

theorem completed_context_494_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 494 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_29 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_54 (code/6))))
    (weight completedCredit) 483 Completed.potential 494 0 113 block_494_0.1
  · simpa only [block_494_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_130 (code/6) (by omega)
    have ht := completed_at_122 (code%7776) (by omega)
    simp only [completed_494_0, source_494_0, target_494_0, hs, ht]

#print axioms completed_context_494_0

theorem completed_context_495_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 495 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_29 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_54 (code/6))))
    (weight completedCredit) 483 Completed.potential 495 0 113 block_495_0.1
  · simpa only [block_495_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_130 (code/6) (by omega)
    have ht := completed_at_123 (code%7776) (by omega)
    simp only [completed_495_0, source_495_0, target_495_0, hs, ht]

#print axioms completed_context_495_0

theorem completed_context_497_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 497 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_29 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_54 (code/6))))
    (weight completedCredit) 483 Completed.potential 497 0 113 block_497_0.1
  · simpa only [block_497_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_130 (code/6) (by omega)
    have ht := completed_at_125 (code%7776) (by omega)
    simp only [completed_497_0, source_497_0, target_497_0, hs, ht]

#print axioms completed_context_497_0

#print axioms prefix_checked
end Snake9.CompletedBatch104G589
