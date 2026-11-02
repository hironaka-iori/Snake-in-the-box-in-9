import BoundedPrefixTransfer102
import Context101Group02
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G106
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)) 483 551 6 0 2715
    Completed.n5_114 Completed.n5_74 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_114 (code/6)))) 6 0 2715 = true := by
  exact joint_root_prefix _ 483 551 2715 Completed.n5_114 Completed.n5_74 joint_checked

theorem completed_context_84_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 84 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_114 (code/6))))
    (weight completedCredit) 483 Completed.potential 84 0 34 block_84_0.1
  · simpa only [block_84_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_24 (code/6) (by omega)
    have ht := completed_at_126 (code%7776) (by omega)
    simp only [completed_84_0, source_84_0, target_84_0, hs, ht]

#print axioms completed_context_84_0

theorem completed_context_85_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 85 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_114 (code/6))))
    (weight completedCredit) 483 Completed.potential 85 0 34 block_85_0.1
  · simpa only [block_85_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_24 (code/6) (by omega)
    have ht := completed_at_127 (code%7776) (by omega)
    simp only [completed_85_0, source_85_0, target_85_0, hs, ht]

#print axioms completed_context_85_0

theorem completed_context_88_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 88 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_114 (code/6))))
    (weight completedCredit) 483 Completed.potential 88 0 34 block_88_0.1
  · simpa only [block_88_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_24 (code/6) (by omega)
    have ht := completed_at_131 (code%7776) (by omega)
    simp only [completed_88_0, source_88_0, target_88_0, hs, ht]

#print axioms completed_context_88_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G106
