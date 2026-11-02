import BoundedPrefixTransfer102
import Context101Group08
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G446
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)) 496 602 6 0 3950
    Conditional.n5_89 Conditional.n5_137 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_137 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_89 (code/6)))) 6 0 3950 = true := by
  exact joint_root_prefix _ 496 602 3950 Conditional.n5_89 Conditional.n5_137 joint_checked

theorem conditional_context_351_65 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 351 65 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_137 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_89 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 351 65 122 block_351_65.1
  · simpa only [block_351_65.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_196 (code/6) (by omega)
    have ht := conditional_at_153 (code%7776) (by omega)
    simp only [conditional_351_65, source_351_65, target_351_65, hs, ht]

#print axioms conditional_context_351_65

theorem conditional_context_351_74 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 351 74 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_137 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_89 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 351 74 122 block_351_74.1
  · simpa only [block_351_74.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_205 (code/6) (by omega)
    have ht := conditional_at_153 (code%7776) (by omega)
    simp only [conditional_351_74, source_351_74, target_351_74, hs, ht]

#print axioms conditional_context_351_74

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G446
