import BoundedPrefixTransfer102
import Context101Group10
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G520
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)) 483 551 6 0 2004
    Completed.n5_106 Completed.n5_70 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_70 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_106 (code/6)))) 6 0 2004 = true := by
  exact joint_root_prefix _ 483 551 2004 Completed.n5_106 Completed.n5_70 joint_checked

theorem completed_context_405_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 405 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_70 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_106 (code/6))))
    (weight completedCredit) 483 Completed.potential 405 0 14 block_405_0.1
  · simpa only [block_405_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_112 (code/6) (by omega)
    have ht := completed_at_80 (code%7776) (by omega)
    simp only [completed_405_0, source_405_0, target_405_0, hs, ht]

#print axioms completed_context_405_0

theorem completed_context_425_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 425 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_70 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_106 (code/6))))
    (weight completedCredit) 483 Completed.potential 425 0 14 block_425_0.1
  · simpa only [block_425_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_116 (code/6) (by omega)
    have ht := completed_at_80 (code%7776) (by omega)
    simp only [completed_425_0, source_425_0, target_425_0, hs, ht]

#print axioms completed_context_425_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G520
