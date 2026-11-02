import BoundedPrefixTransfer102
import Context101Group07
import Context101Group08
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group01

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G400
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)) 496 602 6 0 2004
    Conditional.n5_22 Conditional.n5_63 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_63 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_22 (code/6)))) 6 0 2004 = true := by
  exact joint_root_prefix _ 496 602 2004 Conditional.n5_22 Conditional.n5_63 joint_checked

theorem conditional_context_316_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 316 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_63 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_22 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 316 0 14 block_316_0.1
  · simpa only [block_316_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_91 (code/6) (by omega)
    have ht := conditional_at_47 (code%7776) (by omega)
    simp only [conditional_316_0, source_316_0, target_316_0, hs, ht]

#print axioms conditional_context_316_0

theorem conditional_context_336_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 336 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_63 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_22 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 336 0 14 block_336_0.1
  · simpa only [block_336_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_95 (code/6) (by omega)
    have ht := conditional_at_47 (code%7776) (by omega)
    simp only [conditional_336_0, source_336_0, target_336_0, hs, ht]

#print axioms conditional_context_336_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G400
