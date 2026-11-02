import BoundedPrefixTransfer102
import Context101Group09
import Context101Group12
import JointTraversal103
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G503
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)) 496 602 6 0 3522
    Conditional.n5_67 Conditional.n5_131 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_131 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_67 (code/6)))) 6 0 3522 = true := by
  exact joint_root_prefix _ 496 602 3522 Conditional.n5_67 Conditional.n5_131 joint_checked

theorem conditional_context_391_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 391 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_131 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_67 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 391 0 77 block_391_0.1
  · simpa only [block_391_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_109 (code/6) (by omega)
    have ht := conditional_at_120 (code%7776) (by omega)
    simp only [conditional_391_0, source_391_0, target_391_0, hs, ht]

#print axioms conditional_context_391_0

theorem conditional_context_491_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 491 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_131 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_67 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 491 0 77 block_491_0.1
  · simpa only [block_491_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_129 (code/6) (by omega)
    have ht := conditional_at_120 (code%7776) (by omega)
    simp only [conditional_491_0, source_491_0, target_491_0, hs, ht]

#print axioms conditional_context_491_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G503
