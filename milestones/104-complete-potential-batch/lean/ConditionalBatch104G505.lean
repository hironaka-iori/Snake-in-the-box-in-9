import BoundedPrefixTransfer102
import Context101Group09
import Context101Group10
import JointTraversal103
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G505
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)) 496 602 6 0 3906
    Conditional.n5_60 Conditional.n5_37 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_60 (code/6)))) 6 0 3906 = true := by
  exact joint_root_prefix _ 496 602 3906 Conditional.n5_60 Conditional.n5_37 joint_checked

theorem conditional_context_393_17 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 393 17 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_60 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 393 17 113 block_393_17.1
  · simpa only [block_393_17.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_148 (code/6) (by omega)
    have ht := conditional_at_122 (code%7776) (by omega)
    simp only [conditional_393_17, source_393_17, target_393_17, hs, ht]

#print axioms conditional_context_393_17

theorem conditional_context_394_17 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 394 17 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_60 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 394 17 113 block_394_17.1
  · simpa only [block_394_17.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_148 (code/6) (by omega)
    have ht := conditional_at_123 (code%7776) (by omega)
    simp only [conditional_394_17, source_394_17, target_394_17, hs, ht]

#print axioms conditional_context_394_17

theorem conditional_context_396_17 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 396 17 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_60 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 396 17 113 block_396_17.1
  · simpa only [block_396_17.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_148 (code/6) (by omega)
    have ht := conditional_at_125 (code%7776) (by omega)
    simp only [conditional_396_17, source_396_17, target_396_17, hs, ht]

#print axioms conditional_context_396_17

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G505
