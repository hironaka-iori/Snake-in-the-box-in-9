import BoundedPrefixTransfer102
import Context101Group00
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G040
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 18)) 496 602 6 0 2490
    Conditional.n5_51 Conditional.n5_83 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_83 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 18)+min 602 (value Conditional.n5_51 (code/6)))) 6 0 2490 = true := by
  exact joint_root_prefix _ 496 602 2490 Conditional.n5_51 Conditional.n5_83 joint_checked

theorem conditional_context_36_61 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 36 61 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_83 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 18)+min 602 (value Conditional.n5_51 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 36 61 22 block_36_61.1
  · simpa only [block_36_61.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_192 (code/6) (by omega)
    have ht := conditional_at_102 (code%7776) (by omega)
    simp only [conditional_36_61, source_36_61, target_36_61, hs, ht]

#print axioms conditional_context_36_61

theorem conditional_context_37_61 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 37 61 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_83 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 18)+min 602 (value Conditional.n5_51 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 37 61 22 block_37_61.1
  · simpa only [block_37_61.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_192 (code/6) (by omega)
    have ht := conditional_at_103 (code%7776) (by omega)
    simp only [conditional_37_61, source_37_61, target_37_61, hs, ht]

#print axioms conditional_context_37_61

theorem conditional_context_40_61 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 40 61 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_83 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 7106 then 96 else 0)) 18)+min 602 (value Conditional.n5_51 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 40 61 22 block_40_61.1
  · simpa only [block_40_61.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_192 (code/6) (by omega)
    have ht := conditional_at_106 (code%7776) (by omega)
    simp only [conditional_40_61, source_40_61, target_40_61, hs, ht]

#print axioms conditional_context_40_61

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G040
