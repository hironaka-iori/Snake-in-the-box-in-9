import BoundedPrefixTransfer102
import Context101Group09
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G481
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_141 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_83 (code/6)))) 6 0 2297 = true := by
  decide +kernel

theorem conditional_context_356_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 356 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_141 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_83 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 356 0 18 block_356_0.1
  · simpa only [block_356_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_102 (code/6) (by omega)
    have ht := conditional_at_63 (code%7776) (by omega)
    simp only [conditional_356_0, source_356_0, target_356_0, hs, ht]

#print axioms conditional_context_356_0

theorem conditional_context_374_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 374 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_141 (code%7776)) ≤
        120*(code%6+1)+max (max 9 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_83 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 374 0 18 block_374_0.1
  · simpa only [block_374_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_106 (code/6) (by omega)
    have ht := conditional_at_63 (code%7776) (by omega)
    simp only [conditional_374_0, source_374_0, target_374_0, hs, ht]

#print axioms conditional_context_374_0

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G481
