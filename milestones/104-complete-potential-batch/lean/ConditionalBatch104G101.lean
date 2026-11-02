import BoundedPrefixTransfer102
import Context101Group01
import JointTraversal103
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G101
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [rule011] code)) (max (0) 12)) 496 602 6 0 2703
    Conditional.n5_58 Conditional.n5_35 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_35 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [rule011] code)) (max (0) 12)+min 602 (value Conditional.n5_58 (code/6)))) 6 0 2703 = true := by
  exact joint_root_prefix _ 496 602 2703 Conditional.n5_58 Conditional.n5_35 joint_checked

theorem conditional_context_79_34 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 79 34 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_35 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [rule011] code)) (max (0) 12)+min 602 (value Conditional.n5_58 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 79 34 31 block_79_34.1
  · simpa only [block_79_34.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_165 (code/6) (by omega)
    have ht := conditional_at_182 (code%7776) (by omega)
    simp only [conditional_79_34, source_79_34, target_79_34, hs, ht]

#print axioms conditional_context_79_34

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G101
