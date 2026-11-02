import BoundedPrefixTransfer102
import Context101Group10
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G519
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 0)) 483 551 6 0 2711
    Completed.n5_106 Completed.n5_100 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_100 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_106 (code/6)))) 6 0 2711 = true := by
  exact joint_root_prefix _ 483 551 2711 Completed.n5_106 Completed.n5_100 joint_checked

theorem completed_context_404_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 404 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_100 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_106 (code/6))))
    (weight completedCredit) 483 Completed.potential 404 0 33 block_404_0.1
  · simpa only [block_404_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_112 (code/6) (by omega)
    have ht := completed_at_79 (code%7776) (by omega)
    simp only [completed_404_0, source_404_0, target_404_0, hs, ht]

#print axioms completed_context_404_0

theorem completed_context_424_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 424 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_100 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_106 (code/6))))
    (weight completedCredit) 483 Completed.potential 424 0 33 block_424_0.1
  · simpa only [block_424_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_116 (code/6) (by omega)
    have ht := completed_at_79 (code%7776) (by omega)
    simp only [completed_424_0, source_424_0, target_424_0, hs, ht]

#print axioms completed_context_424_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G519
