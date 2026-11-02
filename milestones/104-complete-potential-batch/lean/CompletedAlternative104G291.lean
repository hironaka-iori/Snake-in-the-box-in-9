import BoundedPrefixTransfer102
import Context101Group05
import Context101Group06
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group01

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G291
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 2 (emittedCredit [] code)) (max (0) 0)) 483 551 6 0 3818
    Completed.n5_160 Completed.n5_103 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_103 (code%7776)) ≤
        120*(code%6+1)+max (max 2 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_160 (code/6)))) 6 0 3818 = true := by
  exact joint_root_prefix _ 483 551 3818 Completed.n5_160 Completed.n5_103 joint_checked

theorem completed_context_214_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 214 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_103 (code%7776)) ≤
        120*(code%6+1)+max (max 2 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_160 (code/6))))
    (weight completedCredit) 483 Completed.potential 214 0 100 block_214_0.1
  · simpa only [block_214_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_62 (code/6) (by omega)
    have ht := completed_at_22 (code%7776) (by omega)
    simp only [completed_214_0, source_214_0, target_214_0, hs, ht]

#print axioms completed_context_214_0

theorem completed_context_234_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 234 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_103 (code%7776)) ≤
        120*(code%6+1)+max (max 2 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_160 (code/6))))
    (weight completedCredit) 483 Completed.potential 234 0 100 block_234_0.1
  · simpa only [block_234_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_66 (code/6) (by omega)
    have ht := completed_at_22 (code%7776) (by omega)
    simp only [completed_234_0, source_234_0, target_234_0, hs, ht]

#print axioms completed_context_234_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G291
