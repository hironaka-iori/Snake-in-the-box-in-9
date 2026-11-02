import BoundedPrefixTransfer102
import Context101Group09
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G487
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)) 483 551 6 0 2355
    Completed.n5_67 Completed.n5_160 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_160 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_67 (code/6)))) 6 0 2355 = true := by
  exact joint_root_prefix _ 483 551 2355 Completed.n5_67 Completed.n5_160 joint_checked

theorem completed_context_355_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 355 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_160 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_67 (code/6))))
    (weight completedCredit) 483 Completed.potential 355 0 19 block_355_0.1
  · simpa only [block_355_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_102 (code/6) (by omega)
    have ht := completed_at_62 (code%7776) (by omega)
    simp only [completed_355_0, source_355_0, target_355_0, hs, ht]

#print axioms completed_context_355_0

theorem completed_context_359_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 359 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_160 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_67 (code/6))))
    (weight completedCredit) 483 Completed.potential 359 0 19 block_359_0.1
  · simpa only [block_359_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_102 (code/6) (by omega)
    have ht := completed_at_66 (code%7776) (by omega)
    simp only [completed_359_0, source_359_0, target_359_0, hs, ht]

#print axioms completed_context_359_0

theorem completed_context_372_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 372 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_160 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_67 (code/6))))
    (weight completedCredit) 483 Completed.potential 372 0 19 block_372_0.1
  · simpa only [block_372_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_106 (code/6) (by omega)
    have ht := completed_at_66 (code%7776) (by omega)
    simp only [completed_372_0, source_372_0, target_372_0, hs, ht]

#print axioms completed_context_372_0

theorem completed_context_373_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 373 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_160 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_67 (code/6))))
    (weight completedCredit) 483 Completed.potential 373 0 19 block_373_0.1
  · simpa only [block_373_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_106 (code/6) (by omega)
    have ht := completed_at_62 (code%7776) (by omega)
    simp only [completed_373_0, source_373_0, target_373_0, hs, ht]

#print axioms completed_context_373_0

theorem completed_context_377_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 377 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_160 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_67 (code/6))))
    (weight completedCredit) 483 Completed.potential 377 0 19 block_377_0.1
  · simpa only [block_377_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_106 (code/6) (by omega)
    have ht := completed_at_66 (code%7776) (by omega)
    simp only [completed_377_0, source_377_0, target_377_0, hs, ht]

#print axioms completed_context_377_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G487
