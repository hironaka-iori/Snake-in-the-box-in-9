import BoundedPrefixTransfer102
import Context101Group01
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G089
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_113 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_111 (code/6)))) 6 0 2691 = true := by
  decide +kernel

theorem conditional_context_74_59 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 74 59 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_113 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_111 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 74 59 29 block_74_59.1
  · simpa only [block_74_59.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_190 (code/6) (by omega)
    have ht := conditional_at_113 (code%7776) (by omega)
    simp only [conditional_74_59, source_74_59, target_74_59, hs, ht]

#print axioms conditional_context_74_59

theorem conditional_context_74_64 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 74 64 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_113 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_111 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 74 64 29 block_74_64.1
  · simpa only [block_74_64.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_195 (code/6) (by omega)
    have ht := conditional_at_113 (code%7776) (by omega)
    simp only [conditional_74_64, source_74_64, target_74_64, hs, ht]

#print axioms conditional_context_74_64

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G089
