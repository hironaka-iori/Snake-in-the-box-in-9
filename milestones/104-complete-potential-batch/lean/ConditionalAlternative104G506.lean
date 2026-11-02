import BoundedPrefixTransfer102
import Context101Group10
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G506
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_56 (code/6)))) 6 0 3906 = true := by
  decide +kernel

theorem conditional_context_393_30 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 393 30 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_56 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 393 30 113 block_393_30.1
  · simpa only [block_393_30.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_161 (code/6) (by omega)
    have ht := conditional_at_122 (code%7776) (by omega)
    simp only [conditional_393_30, source_393_30, target_393_30, hs, ht]

#print axioms conditional_context_393_30

theorem conditional_context_394_30 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 394 30 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_56 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 394 30 113 block_394_30.1
  · simpa only [block_394_30.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_161 (code/6) (by omega)
    have ht := conditional_at_123 (code%7776) (by omega)
    simp only [conditional_394_30, source_394_30, target_394_30, hs, ht]

#print axioms conditional_context_394_30

theorem conditional_context_396_30 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 396 30 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_56 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 396 30 113 block_396_30.1
  · simpa only [block_396_30.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_161 (code/6) (by omega)
    have ht := conditional_at_125 (code%7776) (by omega)
    simp only [conditional_396_30, source_396_30, target_396_30, hs, ht]

#print axioms conditional_context_396_30

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G506
