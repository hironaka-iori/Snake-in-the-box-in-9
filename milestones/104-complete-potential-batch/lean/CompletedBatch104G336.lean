import BoundedPrefixTransfer102
import Context101Group06
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G336
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_61 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [rule024] code)) (max ((if code%7776 = 3221 then 96 else 0)) 0)+min 551 (value Completed.n5_69 (code/6)))) 6 0 3908 = true := by
  decide +kernel

theorem completed_context_264_45 :
    contextCheck (weight completedCredit) 483 Completed.potential 264 45 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_61 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [rule024] code)) (max ((if code%7776 = 3221 then 96 else 0)) 0)+min 551 (value Completed.n5_69 (code/6))))
    (weight completedCredit) 483 Completed.potential 264 45 114 block_264_45.1
  · simpa only [block_264_45.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_176 (code/6) (by omega)
    have ht := completed_at_148 (code%7776) (by omega)
    simp only [completed_264_45, source_264_45, target_264_45, hs, ht]

#print axioms completed_context_264_45

#print axioms prefix_checked
end Snake9.CompletedBatch104G336
