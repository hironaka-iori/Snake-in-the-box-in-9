import BoundedPrefixTransfer102
import Context101Group04
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G209
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)) 496 602 6 0 3579
    Conditional.n5_160 Conditional.n5_135 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_135 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_160 (code/6)))) 6 0 3579 = true := by
  exact joint_root_prefix _ 496 602 3579 Conditional.n5_160 Conditional.n5_135 joint_checked

theorem conditional_context_176_43 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 176 43 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_135 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_160 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 176 43 83 block_176_43.1
  · simpa only [block_176_43.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_174 (code/6) (by omega)
    have ht := conditional_at_18 (code%7776) (by omega)
    simp only [conditional_176_43, source_176_43, target_176_43, hs, ht]

#print axioms conditional_context_176_43

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G209
