import BoundedPrefixTransfer102
import Context101Group03
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group01

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G159
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_7 (code%7776)) ≤
        120*(code%6+1)+max (max 11 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_134 (code/6)))) 6 0 3473 = true := by
  decide +kernel

theorem conditional_context_127_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 127 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_7 (code%7776)) ≤
        120*(code%6+1)+max (max 11 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_134 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 127 0 62 block_127_0.1
  · simpa only [block_127_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_37 (code/6) (by omega)
    have ht := conditional_at_89 (code%7776) (by omega)
    simp only [conditional_127_0, source_127_0, target_127_0, hs, ht]

#print axioms conditional_context_127_0

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G159
