import BoundedPrefixTransfer102
import Context101Group10
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G531
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_26 (code%7776)) ≤
        120*(code%6+1)+max (max 7 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_93 (code/6)))) 6 0 3906 = true := by
  decide +kernel

theorem completed_context_418_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 418 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_26 (code%7776)) ≤
        120*(code%6+1)+max (max 7 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_93 (code/6))))
    (weight completedCredit) 483 Completed.potential 418 0 113 block_418_0.1
  · simpa only [block_418_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_115 (code/6) (by omega)
    have ht := completed_at_77 (code%7776) (by omega)
    simp only [completed_418_0, source_418_0, target_418_0, hs, ht]

#print axioms completed_context_418_0

theorem completed_context_421_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 421 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_26 (code%7776)) ≤
        120*(code%6+1)+max (max 7 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_93 (code/6))))
    (weight completedCredit) 483 Completed.potential 421 0 113 block_421_0.1
  · simpa only [block_421_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_115 (code/6) (by omega)
    have ht := completed_at_77 (code%7776) (by omega)
    simp only [completed_421_0, source_421_0, target_421_0, hs, ht]

#print axioms completed_context_421_0

#print axioms prefix_checked
end Snake9.CompletedBatch104G531
