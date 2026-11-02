import BoundedPrefixTransfer102
import Context101Group10
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G508
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 12)) 496 602 6 0 2703
    Conditional.n5_60 Conditional.n5_47 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_47 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 12)+min 602 (value Conditional.n5_60 (code/6)))) 6 0 2703 = true := by
  exact joint_root_prefix _ 496 602 2703 Conditional.n5_60 Conditional.n5_47 joint_checked

theorem conditional_context_395_17 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 395 17 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_47 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 12)+min 602 (value Conditional.n5_60 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 395 17 31 block_395_17.1
  · simpa only [block_395_17.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_148 (code/6) (by omega)
    have ht := conditional_at_185 (code%7776) (by omega)
    simp only [conditional_395_17, source_395_17, target_395_17, hs, ht]

#print axioms conditional_context_395_17

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G508
