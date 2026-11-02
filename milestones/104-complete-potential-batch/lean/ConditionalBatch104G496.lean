import BoundedPrefixTransfer102
import Context101Group09
import Context101Group10
import Context101Group11
import Context101Group12
import JointTraversal103
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G496
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)) 496 602 6 0 3908
    Conditional.n5_64 Conditional.n5_53 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_53 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_64 (code/6)))) 6 0 3908 = true := by
  exact joint_root_prefix _ 496 602 3908 Conditional.n5_64 Conditional.n5_53 joint_checked

theorem conditional_context_381_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 381 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_53 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_64 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 381 0 114 block_381_0.1
  · simpa only [block_381_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_107 (code/6) (by omega)
    have ht := conditional_at_110 (code%7776) (by omega)
    simp only [conditional_381_0, source_381_0, target_381_0, hs, ht]

#print axioms conditional_context_381_0

theorem conditional_context_401_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 401 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_53 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_64 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 401 0 114 block_401_0.1
  · simpa only [block_401_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_111 (code/6) (by omega)
    have ht := conditional_at_130 (code%7776) (by omega)
    simp only [conditional_401_0, source_401_0, target_401_0, hs, ht]

#print axioms conditional_context_401_0

theorem conditional_context_473_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 473 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_53 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_64 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 473 0 114 block_473_0.1
  · simpa only [block_473_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_126 (code/6) (by omega)
    have ht := conditional_at_130 (code%7776) (by omega)
    simp only [conditional_473_0, source_473_0, target_473_0, hs, ht]

#print axioms conditional_context_473_0

theorem conditional_context_503_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 503 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_53 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_64 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 503 0 114 block_503_0.1
  · simpa only [block_503_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_131 (code/6) (by omega)
    have ht := conditional_at_130 (code%7776) (by omega)
    simp only [conditional_503_0, source_503_0, target_503_0, hs, ht]

#print axioms conditional_context_503_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G496
