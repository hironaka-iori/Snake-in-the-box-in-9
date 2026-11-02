import BoundedPrefixTransfer102
import Context101Group07
import JointTraversal103
import PotentialRoots102Group01
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G352
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_64 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_65 (code/6)))) 6 0 2715 = true := by
  decide +kernel

theorem conditional_context_284_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 284 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_64 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_65 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 284 0 34 block_284_0.1
  · simpa only [block_284_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_82 (code/6) (by omega)
    have ht := conditional_at_126 (code%7776) (by omega)
    simp only [conditional_284_0, source_284_0, target_284_0, hs, ht]

#print axioms conditional_context_284_0

theorem conditional_context_285_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 285 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_64 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_65 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 285 0 34 block_285_0.1
  · simpa only [block_285_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_82 (code/6) (by omega)
    have ht := conditional_at_127 (code%7776) (by omega)
    simp only [conditional_285_0, source_285_0, target_285_0, hs, ht]

#print axioms conditional_context_285_0

theorem conditional_context_288_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 288 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_64 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_65 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 288 0 34 block_288_0.1
  · simpa only [block_288_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_82 (code/6) (by omega)
    have ht := conditional_at_131 (code%7776) (by omega)
    simp only [conditional_288_0, source_288_0, target_288_0, hs, ht]

#print axioms conditional_context_288_0

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G352
