import BoundedPrefixTransfer102
import Context101Group11
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G550
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)) 483 551 6 0 3936
    Completed.n5_29 Completed.n5_67 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_67 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_29 (code/6)))) 6 0 3936 = true := by
  exact joint_root_prefix _ 483 551 3936 Completed.n5_29 Completed.n5_67 joint_checked

theorem completed_context_450_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 450 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_67 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_29 (code/6))))
    (weight completedCredit) 483 Completed.potential 450 0 119 block_450_0.1
  · simpa only [block_450_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_122 (code/6) (by omega)
    have ht := completed_at_102 (code%7776) (by omega)
    simp only [completed_450_0, source_450_0, target_450_0, hs, ht]

#print axioms completed_context_450_0

theorem completed_context_451_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 451 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_67 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_29 (code/6))))
    (weight completedCredit) 483 Completed.potential 451 0 119 block_451_0.1
  · simpa only [block_451_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_122 (code/6) (by omega)
    have ht := completed_at_103 (code%7776) (by omega)
    simp only [completed_451_0, source_451_0, target_451_0, hs, ht]

#print axioms completed_context_451_0

theorem completed_context_454_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 454 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_67 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_29 (code/6))))
    (weight completedCredit) 483 Completed.potential 454 0 119 block_454_0.1
  · simpa only [block_454_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_122 (code/6) (by omega)
    have ht := completed_at_106 (code%7776) (by omega)
    simp only [completed_454_0, source_454_0, target_454_0, hs, ht]

#print axioms completed_context_454_0

theorem completed_context_463_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 463 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_67 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_29 (code/6))))
    (weight completedCredit) 483 Completed.potential 463 0 119 block_463_0.1
  · simpa only [block_463_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_125 (code/6) (by omega)
    have ht := completed_at_106 (code%7776) (by omega)
    simp only [completed_463_0, source_463_0, target_463_0, hs, ht]

#print axioms completed_context_463_0

theorem completed_context_464_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 464 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_67 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_29 (code/6))))
    (weight completedCredit) 483 Completed.potential 464 0 119 block_464_0.1
  · simpa only [block_464_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_125 (code/6) (by omega)
    have ht := completed_at_102 (code%7776) (by omega)
    simp only [completed_464_0, source_464_0, target_464_0, hs, ht]

#print axioms completed_context_464_0

theorem completed_context_465_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 465 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_67 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_29 (code/6))))
    (weight completedCredit) 483 Completed.potential 465 0 119 block_465_0.1
  · simpa only [block_465_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_125 (code/6) (by omega)
    have ht := completed_at_103 (code%7776) (by omega)
    simp only [completed_465_0, source_465_0, target_465_0, hs, ht]

#print axioms completed_context_465_0

theorem completed_context_468_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 468 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_67 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 0)+min 551 (value Completed.n5_29 (code/6))))
    (weight completedCredit) 483 Completed.potential 468 0 119 block_468_0.1
  · simpa only [block_468_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_125 (code/6) (by omega)
    have ht := completed_at_106 (code%7776) (by omega)
    simp only [completed_468_0, source_468_0, target_468_0, hs, ht]

#print axioms completed_context_468_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G550
