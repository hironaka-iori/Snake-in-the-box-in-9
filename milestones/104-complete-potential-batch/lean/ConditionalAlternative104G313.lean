import BoundedPrefixTransfer102
import Context101Group06
import JointTraversal103
import PotentialRoots102Group01

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G313
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_54 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_109 (code/6)))) 6 0 3908 = true := by
  decide +kernel

theorem conditional_context_242_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 242 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_54 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_109 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 242 0 114 block_242_0.1
  · simpa only [block_242_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_70 (code/6) (by omega)
    have ht := conditional_at_81 (code%7776) (by omega)
    simp only [conditional_242_0, source_242_0, target_242_0, hs, ht]

#print axioms conditional_context_242_0

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G313
