import BoundedPrefixTransfer102
import Context101Group11
import JointTraversal103
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G573
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_78 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [rule029] code)) (max ((if code%7776 = 7106 then 96 else 0)) 18)+min 602 (value Conditional.n5_35 (code/6)))) 6 0 3938 = true := by
  decide +kernel

theorem conditional_context_462_51 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 462 51 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_78 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [rule029] code)) (max ((if code%7776 = 7106 then 96 else 0)) 18)+min 602 (value Conditional.n5_35 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 462 51 120 block_462_51.1
  · simpa only [block_462_51.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_182 (code/6) (by omega)
    have ht := conditional_at_160 (code%7776) (by omega)
    simp only [conditional_462_51, source_462_51, target_462_51, hs, ht]

#print axioms conditional_context_462_51

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G573
