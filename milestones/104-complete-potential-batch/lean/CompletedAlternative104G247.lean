import BoundedPrefixTransfer102
import Context101Group04
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G247
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 0)) 483 551 6 0 3779
    Completed.n5_175 Completed.n5_101 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_101 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_175 (code/6)))) 6 0 3779 = true := by
  exact joint_root_prefix _ 483 551 3779 Completed.n5_175 Completed.n5_101 joint_checked

theorem completed_context_182_21 :
    contextCheck (weight completedCredit) 483 Completed.potential 182 21 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_101 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_175 (code/6))))
    (weight completedCredit) 483 Completed.potential 182 21 91 block_182_21.1
  · simpa only [block_182_21.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_152 (code/6) (by omega)
    have ht := completed_at_190 (code%7776) (by omega)
    simp only [completed_182_21, source_182_21, target_182_21, hs, ht]

#print axioms completed_context_182_21

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G247
