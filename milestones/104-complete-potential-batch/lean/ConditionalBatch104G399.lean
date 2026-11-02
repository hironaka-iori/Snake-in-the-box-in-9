import BoundedPrefixTransfer102
import Context101Group07
import Context101Group08
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group01

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G399
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)) 496 602 6 0 1698
    Conditional.n5_22 Conditional.n5_104 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_104 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_22 (code/6)))) 6 0 1698 = true := by
  exact joint_root_prefix _ 496 602 1698 Conditional.n5_22 Conditional.n5_104 joint_checked

theorem conditional_context_315_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 315 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_104 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_22 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 315 0 11 block_315_0.1
  · simpa only [block_315_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_91 (code/6) (by omega)
    have ht := conditional_at_46 (code%7776) (by omega)
    simp only [conditional_315_0, source_315_0, target_315_0, hs, ht]

#print axioms conditional_context_315_0

theorem conditional_context_335_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 335 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_104 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_22 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 335 0 11 block_335_0.1
  · simpa only [block_335_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_95 (code/6) (by omega)
    have ht := conditional_at_46 (code%7776) (by omega)
    simp only [conditional_335_0, source_335_0, target_335_0, hs, ht]

#print axioms conditional_context_335_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G399
