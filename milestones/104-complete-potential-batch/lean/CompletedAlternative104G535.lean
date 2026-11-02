import BoundedPrefixTransfer102
import Context101Group10
import Context101Group11
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G535
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 13 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)) 483 551 6 0 2979
    Completed.n5_132 Completed.n5_20 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_20 (code%7776)) ≤
        120*(code%6+1)+max (max 13 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_132 (code/6)))) 6 0 2979 = true := by
  exact joint_root_prefix _ 483 551 2979 Completed.n5_132 Completed.n5_20 joint_checked

theorem completed_context_428_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 428 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_20 (code%7776)) ≤
        120*(code%6+1)+max (max 13 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_132 (code/6))))
    (weight completedCredit) 483 Completed.potential 428 0 38 block_428_0.1
  · simpa only [block_428_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_117 (code/6) (by omega)
    have ht := completed_at_91 (code%7776) (by omega)
    simp only [completed_428_0, source_428_0, target_428_0, hs, ht]

#print axioms completed_context_428_0

theorem completed_context_432_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 432 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_20 (code%7776)) ≤
        120*(code%6+1)+max (max 13 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_132 (code/6))))
    (weight completedCredit) 483 Completed.potential 432 0 38 block_432_0.1
  · simpa only [block_432_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_117 (code/6) (by omega)
    have ht := completed_at_95 (code%7776) (by omega)
    simp only [completed_432_0, source_432_0, target_432_0, hs, ht]

#print axioms completed_context_432_0

theorem completed_context_444_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 444 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_20 (code%7776)) ≤
        120*(code%6+1)+max (max 13 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_132 (code/6))))
    (weight completedCredit) 483 Completed.potential 444 0 38 block_444_0.1
  · simpa only [block_444_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_121 (code/6) (by omega)
    have ht := completed_at_95 (code%7776) (by omega)
    simp only [completed_444_0, source_444_0, target_444_0, hs, ht]

#print axioms completed_context_444_0

theorem completed_context_445_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 445 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_20 (code%7776)) ≤
        120*(code%6+1)+max (max 13 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_132 (code/6))))
    (weight completedCredit) 483 Completed.potential 445 0 38 block_445_0.1
  · simpa only [block_445_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_121 (code/6) (by omega)
    have ht := completed_at_91 (code%7776) (by omega)
    simp only [completed_445_0, source_445_0, target_445_0, hs, ht]

#print axioms completed_context_445_0

theorem completed_context_449_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 449 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_20 (code%7776)) ≤
        120*(code%6+1)+max (max 13 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_132 (code/6))))
    (weight completedCredit) 483 Completed.potential 449 0 38 block_449_0.1
  · simpa only [block_449_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_121 (code/6) (by omega)
    have ht := completed_at_95 (code%7776) (by omega)
    simp only [completed_449_0, source_449_0, target_449_0, hs, ht]

#print axioms completed_context_449_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G535
