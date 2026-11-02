import BoundedPrefixTransfer102
import Context101Group09
import JointTraversal103
import PotentialRoots102Group01

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G484
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_157 (code%7776)) ≤
        120*(code%6+1)+max (max 33 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_83 (code/6)))) 6 0 2355 = true := by
  decide +kernel

theorem conditional_context_360_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 360 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_157 (code%7776)) ≤
        120*(code%6+1)+max (max 33 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_83 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 360 0 19 block_360_0.1
  · simpa only [block_360_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_103 (code/6) (by omega)
    have ht := conditional_at_56 (code%7776) (by omega)
    simp only [conditional_360_0, source_360_0, target_360_0, hs, ht]

#print axioms conditional_context_360_0

theorem conditional_context_364_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 364 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_157 (code%7776)) ≤
        120*(code%6+1)+max (max 33 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_83 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 364 0 19 block_364_0.1
  · simpa only [block_364_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_103 (code/6) (by omega)
    have ht := conditional_at_56 (code%7776) (by omega)
    simp only [conditional_364_0, source_364_0, target_364_0, hs, ht]

#print axioms conditional_context_364_0

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G484
