import BoundedPrefixTransfer102
import Context101Group04
import JointTraversal103
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G249
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)) 496 602 6 0 3779
    Conditional.n5_154 Conditional.n5_111 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_111 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_154 (code/6)))) 6 0 3779 = true := by
  exact joint_root_prefix _ 496 602 3779 Conditional.n5_154 Conditional.n5_111 joint_checked

theorem conditional_context_182_52 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 182 52 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_111 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_154 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 182 52 91 block_182_52.1
  · simpa only [block_182_52.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_183 (code/6) (by omega)
    have ht := conditional_at_190 (code%7776) (by omega)
    simp only [conditional_182_52, source_182_52, target_182_52, hs, ht]

#print axioms conditional_context_182_52

theorem conditional_context_182_53 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 182 53 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_111 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_154 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 182 53 91 block_182_53.1
  · simpa only [block_182_53.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_184 (code/6) (by omega)
    have ht := conditional_at_195 (code%7776) (by omega)
    simp only [conditional_182_53, source_182_53, target_182_53, hs, ht]

#print axioms conditional_context_182_53

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G249
