import BoundedPrefixTransfer102
import Context101Group10
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G522
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_68 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_106 (code/6)))) 6 0 2715 = true := by
  decide +kernel

theorem completed_context_407_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 407 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_68 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_106 (code/6))))
    (weight completedCredit) 483 Completed.potential 407 0 34 block_407_0.1
  · simpa only [block_407_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_112 (code/6) (by omega)
    have ht := completed_at_82 (code%7776) (by omega)
    simp only [completed_407_0, source_407_0, target_407_0, hs, ht]

#print axioms completed_context_407_0

theorem completed_context_422_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 422 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_68 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_106 (code/6))))
    (weight completedCredit) 483 Completed.potential 422 0 34 block_422_0.1
  · simpa only [block_422_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_116 (code/6) (by omega)
    have ht := completed_at_82 (code%7776) (by omega)
    simp only [completed_422_0, source_422_0, target_422_0, hs, ht]

#print axioms completed_context_422_0

theorem completed_context_427_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 427 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_68 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_106 (code/6))))
    (weight completedCredit) 483 Completed.potential 427 0 34 block_427_0.1
  · simpa only [block_427_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_116 (code/6) (by omega)
    have ht := completed_at_82 (code%7776) (by omega)
    simp only [completed_427_0, source_427_0, target_427_0, hs, ht]

#print axioms completed_context_427_0

#print axioms prefix_checked
end Snake9.CompletedBatch104G522
