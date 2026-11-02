import BoundedPrefixTransfer102
import Context101Group04
import JointTraversal103
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G197
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 12)) 496 602 6 0 3544
    Conditional.n5_138 Conditional.n5_49 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_49 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 12)+min 602 (value Conditional.n5_138 (code/6)))) 6 0 3544 = true := by
  exact joint_root_prefix _ 496 602 3544 Conditional.n5_138 Conditional.n5_49 joint_checked

theorem conditional_context_171_36 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 171 36 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_49 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 12)+min 602 (value Conditional.n5_138 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 171 36 79 block_171_36.1
  · simpa only [block_171_36.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_167 (code/6) (by omega)
    have ht := conditional_at_191 (code%7776) (by omega)
    simp only [conditional_171_36, source_171_36, target_171_36, hs, ht]

#print axioms conditional_context_171_36

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G197
