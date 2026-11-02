import BoundedPrefixTransfer102
import Context101Group09
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G482
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (0) 16)) 496 602 6 0 2231
    Conditional.n5_83 Conditional.n5_167 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_167 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_83 (code/6)))) 6 0 2231 = true := by
  exact joint_root_prefix _ 496 602 2231 Conditional.n5_83 Conditional.n5_167 joint_checked

theorem conditional_context_357_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 357 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_167 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_83 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 357 0 17 block_357_0.1
  · simpa only [block_357_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_102 (code/6) (by omega)
    have ht := conditional_at_64 (code%7776) (by omega)
    simp only [conditional_357_0, source_357_0, target_357_0, hs, ht]

#print axioms conditional_context_357_0

theorem conditional_context_375_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 375 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_167 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_83 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 375 0 17 block_375_0.1
  · simpa only [block_375_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_106 (code/6) (by omega)
    have ht := conditional_at_64 (code%7776) (by omega)
    simp only [conditional_375_0, source_375_0, target_375_0, hs, ht]

#print axioms conditional_context_375_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G482
