import BoundedPrefixTransfer102
import Context101Group08
import JointTraversal103
import PotentialRoots102Group01

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G416
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)) 496 602 6 0 2418
    Conditional.n5_44 Conditional.n5_142 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_142 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_44 (code/6)))) 6 0 2418 = true := by
  exact joint_root_prefix _ 496 602 2418 Conditional.n5_44 Conditional.n5_142 joint_checked

theorem conditional_context_342_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 342 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_142 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_44 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 342 0 20 block_342_0.1
  · simpa only [block_342_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_98 (code/6) (by omega)
    have ht := conditional_at_61 (code%7776) (by omega)
    simp only [conditional_342_0, source_342_0, target_342_0, hs, ht]

#print axioms conditional_context_342_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G416
