import BoundedPrefixTransfer102
import Context101Group00
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G039
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_67 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_42 (code/6)))) 6 0 2490 = true := by
  decide +kernel

theorem completed_context_36_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 36 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_67 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_42 (code/6))))
    (weight completedCredit) 483 Completed.potential 36 0 22 block_36_0.1
  · simpa only [block_36_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_11 (code/6) (by omega)
    have ht := completed_at_102 (code%7776) (by omega)
    simp only [completed_36_0, source_36_0, target_36_0, hs, ht]

#print axioms completed_context_36_0

theorem completed_context_37_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 37 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_67 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_42 (code/6))))
    (weight completedCredit) 483 Completed.potential 37 0 22 block_37_0.1
  · simpa only [block_37_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_11 (code/6) (by omega)
    have ht := completed_at_103 (code%7776) (by omega)
    simp only [completed_37_0, source_37_0, target_37_0, hs, ht]

#print axioms completed_context_37_0

theorem completed_context_40_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 40 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_67 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_42 (code/6))))
    (weight completedCredit) 483 Completed.potential 40 0 22 block_40_0.1
  · simpa only [block_40_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_11 (code/6) (by omega)
    have ht := completed_at_106 (code%7776) (by omega)
    simp only [completed_40_0, source_40_0, target_40_0, hs, ht]

#print axioms completed_context_40_0

#print axioms prefix_checked
end Snake9.CompletedBatch104G039
