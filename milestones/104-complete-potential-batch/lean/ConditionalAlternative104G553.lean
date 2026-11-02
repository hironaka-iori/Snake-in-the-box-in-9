import BoundedPrefixTransfer102
import Context101Group11
import JointTraversal103
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G553
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_88 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [rule016] code)) (max ((if code%7776 = 7106 then 96 else 0)) 18)+min 602 (value Conditional.n5_147 (code/6)))) 6 0 3938 = true := by
  decide +kernel

theorem conditional_context_460_41 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 460 41 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_88 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [rule016] code)) (max ((if code%7776 = 7106 then 96 else 0)) 18)+min 602 (value Conditional.n5_147 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 460 41 120 block_460_41.1
  · simpa only [block_460_41.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_172 (code/6) (by omega)
    have ht := conditional_at_175 (code%7776) (by omega)
    simp only [conditional_460_41, source_460_41, target_460_41, hs, ht]

#print axioms conditional_context_460_41

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G553
