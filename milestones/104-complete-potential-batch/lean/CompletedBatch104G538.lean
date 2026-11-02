import BoundedPrefixTransfer102
import Context101Group10
import Context101Group11
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G538
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_13 (code%7776)) ≤
        120*(code%6+1)+max (max 13 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 0)+min 551 (value Completed.n5_132 (code/6)))) 6 0 3910 = true := by
  decide +kernel

theorem completed_context_431_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 431 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_13 (code%7776)) ≤
        120*(code%6+1)+max (max 13 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 0)+min 551 (value Completed.n5_132 (code/6))))
    (weight completedCredit) 483 Completed.potential 431 0 115 block_431_0.1
  · simpa only [block_431_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_117 (code/6) (by omega)
    have ht := completed_at_94 (code%7776) (by omega)
    simp only [completed_431_0, source_431_0, target_431_0, hs, ht]

#print axioms completed_context_431_0

theorem completed_context_448_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 448 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_13 (code%7776)) ≤
        120*(code%6+1)+max (max 13 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 0)+min 551 (value Completed.n5_132 (code/6))))
    (weight completedCredit) 483 Completed.potential 448 0 115 block_448_0.1
  · simpa only [block_448_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_121 (code/6) (by omega)
    have ht := completed_at_94 (code%7776) (by omega)
    simp only [completed_448_0, source_448_0, target_448_0, hs, ht]

#print axioms completed_context_448_0

#print axioms prefix_checked
end Snake9.CompletedBatch104G538
