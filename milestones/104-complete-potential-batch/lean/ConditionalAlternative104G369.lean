import BoundedPrefixTransfer102
import Context101Group07
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G369
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_17 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_5 (code/6)))) 6 0 3835 = true := by
  decide +kernel

theorem conditional_context_300_5 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 300 5 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_17 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_5 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 300 5 103 block_300_5.1
  · simpa only [block_300_5.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_136 (code/6) (by omega)
    have ht := conditional_at_168 (code%7776) (by omega)
    simp only [conditional_300_5, source_300_5, target_300_5, hs, ht]

#print axioms conditional_context_300_5

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G369
