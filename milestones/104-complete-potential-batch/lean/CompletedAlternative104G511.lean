import BoundedPrefixTransfer102
import Context101Group09
import Context101Group10
import JointTraversal103
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G511
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)) 483 551 6 0 3906
    Completed.n5_55 Completed.n5_29 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_29 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_55 (code/6)))) 6 0 3906 = true := by
  exact joint_root_prefix _ 483 551 3906 Completed.n5_55 Completed.n5_29 joint_checked

theorem completed_context_393_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 393 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_29 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_55 (code/6))))
    (weight completedCredit) 483 Completed.potential 393 0 113 block_393_0.1
  · simpa only [block_393_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_110 (code/6) (by omega)
    have ht := completed_at_122 (code%7776) (by omega)
    simp only [completed_393_0, source_393_0, target_393_0, hs, ht]

#print axioms completed_context_393_0

theorem completed_context_394_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 394 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_29 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_55 (code/6))))
    (weight completedCredit) 483 Completed.potential 394 0 113 block_394_0.1
  · simpa only [block_394_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_110 (code/6) (by omega)
    have ht := completed_at_123 (code%7776) (by omega)
    simp only [completed_394_0, source_394_0, target_394_0, hs, ht]

#print axioms completed_context_394_0

theorem completed_context_396_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 396 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_29 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_55 (code/6))))
    (weight completedCredit) 483 Completed.potential 396 0 113 block_396_0.1
  · simpa only [block_396_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_110 (code/6) (by omega)
    have ht := completed_at_125 (code%7776) (by omega)
    simp only [completed_396_0, source_396_0, target_396_0, hs, ht]

#print axioms completed_context_396_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G511
