import BoundedPrefixTransfer102
import Context101Group09
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G491
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)) 496 602 6 0 2418
    Conditional.n5_39 Conditional.n5_142 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_142 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_39 (code/6)))) 6 0 2418 = true := by
  exact joint_root_prefix _ 496 602 2418 Conditional.n5_39 Conditional.n5_142 joint_checked

theorem conditional_context_369_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 369 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_142 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_39 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 369 0 20 block_369_0.1
  · simpa only [block_369_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_105 (code/6) (by omega)
    have ht := conditional_at_61 (code%7776) (by omega)
    simp only [conditional_369_0, source_369_0, target_369_0, hs, ht]

#print axioms conditional_context_369_0

theorem conditional_context_371_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 371 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_142 (code%7776)) ≤
        120*(code%6+1)+max (max 10 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_39 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 371 0 20 block_371_0.1
  · simpa only [block_371_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_105 (code/6) (by omega)
    have ht := conditional_at_61 (code%7776) (by omega)
    simp only [conditional_371_0, source_371_0, target_371_0, hs, ht]

#print axioms conditional_context_371_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G491
