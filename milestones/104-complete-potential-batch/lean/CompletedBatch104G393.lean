import BoundedPrefixTransfer102
import Context101Group07
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G393
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_15 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [rule025] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_4 (code/6)))) 6 0 3835 = true := by
  decide +kernel

theorem completed_context_305_47 :
    contextCheck (weight completedCredit) 483 Completed.potential 305 47 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_15 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [rule025] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_4 (code/6))))
    (weight completedCredit) 483 Completed.potential 305 47 103 block_305_47.1
  · simpa only [block_305_47.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_178 (code/6) (by omega)
    have ht := completed_at_151 (code%7776) (by omega)
    simp only [completed_305_47, source_305_47, target_305_47, hs, ht]

#print axioms completed_context_305_47

#print axioms prefix_checked
end Snake9.CompletedBatch104G393
