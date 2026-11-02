import BoundedPrefixTransfer102
import Context101Group04
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G231
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)) 483 551 6 0 3713
    Completed.n5_155 Completed.n5_117 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_117 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_155 (code/6)))) 6 0 3713 = true := by
  exact joint_root_prefix _ 483 551 3713 Completed.n5_155 Completed.n5_117 joint_checked

theorem completed_context_180_24 :
    contextCheck (weight completedCredit) 483 Completed.potential 180 24 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_117 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_155 (code/6))))
    (weight completedCredit) 483 Completed.potential 180 24 88 block_180_24.1
  · simpa only [block_180_24.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_155 (code/6) (by omega)
    have ht := completed_at_20 (code%7776) (by omega)
    simp only [completed_180_24, source_180_24, target_180_24, hs, ht]

#print axioms completed_context_180_24

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G231
