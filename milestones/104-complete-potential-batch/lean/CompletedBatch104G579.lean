import BoundedPrefixTransfer102
import Context101Group11
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G579
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_85 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_45 (code/6)))) 6 0 3938 = true := by
  decide +kernel

theorem completed_context_462_18 :
    contextCheck (weight completedCredit) 483 Completed.potential 462 18 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_85 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_45 (code/6))))
    (weight completedCredit) 483 Completed.potential 462 18 120 block_462_18.1
  · simpa only [block_462_18.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_149 (code/6) (by omega)
    have ht := completed_at_160 (code%7776) (by omega)
    simp only [completed_462_18, source_462_18, target_462_18, hs, ht]

#print axioms completed_context_462_18

#print axioms prefix_checked
end Snake9.CompletedBatch104G579
