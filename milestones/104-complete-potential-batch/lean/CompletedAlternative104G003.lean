import BoundedPrefixTransfer102
import Context101Group00
import JointTraversal103
import PotentialRoots102Group00

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G003
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)) 483 551 6 0 379
    Completed.n5_5 Completed.n5_82 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_82 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_5 (code/6)))) 6 0 379 = true := by
  exact joint_root_prefix _ 483 551 379 Completed.n5_5 Completed.n5_82 joint_checked

theorem completed_context_3_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 3 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_82 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_5 (code/6))))
    (weight completedCredit) 483 Completed.potential 3 0 1 block_3_0.1
  · simpa only [block_3_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_0 (code/6) (by omega)
    have ht := completed_at_32 (code%7776) (by omega)
    simp only [completed_3_0, source_3_0, target_3_0, hs, ht]

#print axioms completed_context_3_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G003
