import BoundedPrefixTransfer102
import Context101Group08
import JointTraversal103
import PotentialRoots102Group01

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G420
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)) 483 551 6 0 2355
    Completed.n5_77 Completed.n5_160 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_160 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_77 (code/6)))) 6 0 2355 = true := by
  exact joint_root_prefix _ 483 551 2355 Completed.n5_77 Completed.n5_160 joint_checked

theorem completed_context_343_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 343 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_160 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_77 (code/6))))
    (weight completedCredit) 483 Completed.potential 343 0 19 block_343_0.1
  · simpa only [block_343_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_99 (code/6) (by omega)
    have ht := completed_at_62 (code%7776) (by omega)
    simp only [completed_343_0, source_343_0, target_343_0, hs, ht]

#print axioms completed_context_343_0

theorem completed_context_347_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 347 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_160 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_77 (code/6))))
    (weight completedCredit) 483 Completed.potential 347 0 19 block_347_0.1
  · simpa only [block_347_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_99 (code/6) (by omega)
    have ht := completed_at_66 (code%7776) (by omega)
    simp only [completed_347_0, source_347_0, target_347_0, hs, ht]

#print axioms completed_context_347_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G420
