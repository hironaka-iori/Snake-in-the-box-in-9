import BoundedPrefixTransfer102
import Context101Group07
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G378
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_9 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_0 (code/6)))) 6 0 3849 = true := by
  decide +kernel

theorem conditional_context_302_47 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 302 47 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_9 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_0 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 302 47 105 block_302_47.1
  · simpa only [block_302_47.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_178 (code/6) (by omega)
    have ht := conditional_at_150 (code%7776) (by omega)
    simp only [conditional_302_47, source_302_47, target_302_47, hs, ht]

#print axioms conditional_context_302_47

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G378
