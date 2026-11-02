import BoundedPrefixTransfer102
import Context101Group04
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G219
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 20 (emittedCredit [] code)) (max (0) 16)) 496 602 6 0 3698
    Conditional.n5_158 Conditional.n5_129 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_129 (code%7776)) ≤
        120*(code%6+1)+max (max 20 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_158 (code/6)))) 6 0 3698 = true := by
  exact joint_root_prefix _ 496 602 3698 Conditional.n5_158 Conditional.n5_129 joint_checked

theorem conditional_context_178_70 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 178 70 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_129 (code%7776)) ≤
        120*(code%6+1)+max (max 20 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_158 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 178 70 86 block_178_70.1
  · simpa only [block_178_70.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_201 (code/6) (by omega)
    have ht := conditional_at_19 (code%7776) (by omega)
    simp only [conditional_178_70, source_178_70, target_178_70, hs, ht]

#print axioms conditional_context_178_70

theorem conditional_context_178_72 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 178 72 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_129 (code%7776)) ≤
        120*(code%6+1)+max (max 20 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_158 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 178 72 86 block_178_72.1
  · simpa only [block_178_72.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_203 (code/6) (by omega)
    have ht := conditional_at_19 (code%7776) (by omega)
    simp only [conditional_178_72, source_178_72, target_178_72, hs, ht]

#print axioms conditional_context_178_72

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G219
