import BoundedPrefixTransfer102
import Context101Group09
import JointTraversal103
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G462
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_158 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_79 (code/6)))) 6 0 3980 = true := by
  decide +kernel

theorem conditional_context_353_28 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 353 28 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_158 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_79 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 353 28 125 block_353_28.1
  · simpa only [block_353_28.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_159 (code/6) (by omega)
    have ht := conditional_at_201 (code%7776) (by omega)
    simp only [conditional_353_28, source_353_28, target_353_28, hs, ht]

#print axioms conditional_context_353_28

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G462
