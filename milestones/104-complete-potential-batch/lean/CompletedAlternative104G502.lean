import BoundedPrefixTransfer102
import Context101Group09
import Context101Group10
import Context101Group11
import Context101Group12
import JointTraversal103
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G502
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)) 483 551 6 0 2004
    Completed.n5_74 Completed.n5_76 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_76 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_74 (code/6)))) 6 0 2004 = true := by
  exact joint_root_prefix _ 483 551 2004 Completed.n5_74 Completed.n5_76 joint_checked

theorem completed_context_380_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 380 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_76 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 380 0 14 block_380_0.1
  · simpa only [block_380_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_107 (code/6) (by omega)
    have ht := completed_at_109 (code%7776) (by omega)
    simp only [completed_380_0, source_380_0, target_380_0, hs, ht]

#print axioms completed_context_380_0

theorem completed_context_400_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 400 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_76 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 400 0 14 block_400_0.1
  · simpa only [block_400_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_111 (code/6) (by omega)
    have ht := completed_at_129 (code%7776) (by omega)
    simp only [completed_400_0, source_400_0, target_400_0, hs, ht]

#print axioms completed_context_400_0

theorem completed_context_472_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 472 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_76 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 472 0 14 block_472_0.1
  · simpa only [block_472_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_126 (code/6) (by omega)
    have ht := completed_at_129 (code%7776) (by omega)
    simp only [completed_472_0, source_472_0, target_472_0, hs, ht]

#print axioms completed_context_472_0

theorem completed_context_478_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 478 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_76 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 478 0 14 block_478_0.1
  · simpa only [block_478_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_127 (code/6) (by omega)
    have ht := completed_at_109 (code%7776) (by omega)
    simp only [completed_478_0, source_478_0, target_478_0, hs, ht]

#print axioms completed_context_478_0

theorem completed_context_502_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 502 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_76 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 502 0 14 block_502_0.1
  · simpa only [block_502_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_131 (code/6) (by omega)
    have ht := completed_at_129 (code%7776) (by omega)
    simp only [completed_502_0, source_502_0, target_502_0, hs, ht]

#print axioms completed_context_502_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G502
