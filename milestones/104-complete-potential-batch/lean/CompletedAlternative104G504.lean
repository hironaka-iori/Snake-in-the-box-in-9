import BoundedPrefixTransfer102
import Context101Group09
import Context101Group11
import Context101Group12
import JointTraversal103
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G504
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)) 483 551 6 0 2698
    Completed.n5_102 Completed.n5_106 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_106 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_102 (code/6)))) 6 0 2698 = true := by
  exact joint_root_prefix _ 483 551 2698 Completed.n5_102 Completed.n5_106 joint_checked

theorem completed_context_383_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 383 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_106 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_102 (code/6))))
    (weight completedCredit) 483 Completed.potential 383 0 30 block_383_0.1
  · simpa only [block_383_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_108 (code/6) (by omega)
    have ht := completed_at_112 (code%7776) (by omega)
    simp only [completed_383_0, source_383_0, target_383_0, hs, ht]

#print axioms completed_context_383_0

theorem completed_context_387_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 387 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_106 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_102 (code/6))))
    (weight completedCredit) 483 Completed.potential 387 0 30 block_387_0.1
  · simpa only [block_387_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_108 (code/6) (by omega)
    have ht := completed_at_116 (code%7776) (by omega)
    simp only [completed_387_0, source_387_0, target_387_0, hs, ht]

#print axioms completed_context_387_0

theorem completed_context_481_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 481 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_106 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_102 (code/6))))
    (weight completedCredit) 483 Completed.potential 481 0 30 block_481_0.1
  · simpa only [block_481_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_128 (code/6) (by omega)
    have ht := completed_at_116 (code%7776) (by omega)
    simp only [completed_481_0, source_481_0, target_481_0, hs, ht]

#print axioms completed_context_481_0

theorem completed_context_482_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 482 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_106 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_102 (code/6))))
    (weight completedCredit) 483 Completed.potential 482 0 30 block_482_0.1
  · simpa only [block_482_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_128 (code/6) (by omega)
    have ht := completed_at_112 (code%7776) (by omega)
    simp only [completed_482_0, source_482_0, target_482_0, hs, ht]

#print axioms completed_context_482_0

theorem completed_context_486_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 486 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_106 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_102 (code/6))))
    (weight completedCredit) 483 Completed.potential 486 0 30 block_486_0.1
  · simpa only [block_486_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_128 (code/6) (by omega)
    have ht := completed_at_116 (code%7776) (by omega)
    simp only [completed_486_0, source_486_0, target_486_0, hs, ht]

#print axioms completed_context_486_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G504
