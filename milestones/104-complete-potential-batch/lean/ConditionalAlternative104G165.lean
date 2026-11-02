import BoundedPrefixTransfer102
import Context101Group03
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group01

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G165
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_22 (code%7776)) ≤
        120*(code%6+1)+max (max 13 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_128 (code/6)))) 6 0 3479 = true := by
  decide +kernel

theorem conditional_context_133_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 133 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_22 (code%7776)) ≤
        120*(code%6+1)+max (max 13 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_128 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 133 0 64 block_133_0.1
  · simpa only [block_133_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_40 (code/6) (by omega)
    have ht := conditional_at_91 (code%7776) (by omega)
    simp only [conditional_133_0, source_133_0, target_133_0, hs, ht]

#print axioms conditional_context_133_0

theorem conditional_context_136_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 136 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_22 (code%7776)) ≤
        120*(code%6+1)+max (max 13 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_128 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 136 0 64 block_136_0.1
  · simpa only [block_136_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_40 (code/6) (by omega)
    have ht := conditional_at_95 (code%7776) (by omega)
    simp only [conditional_136_0, source_136_0, target_136_0, hs, ht]

#print axioms conditional_context_136_0

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G165
