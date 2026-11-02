import BoundedPrefixTransfer102
import Context101Group03
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G177
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_52 (code/6)))) 6 0 3508 = true := by
  decide +kernel

theorem conditional_context_145_8 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 145 8 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_52 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 145 8 72 block_145_8.1
  · simpa only [block_145_8.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_139 (code/6) (by omega)
    have ht := conditional_at_122 (code%7776) (by omega)
    simp only [conditional_145_8, source_145_8, target_145_8, hs, ht]

#print axioms conditional_context_145_8

theorem conditional_context_145_57 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 145 57 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_52 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 145 57 72 block_145_57.1
  · simpa only [block_145_57.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_188 (code/6) (by omega)
    have ht := conditional_at_122 (code%7776) (by omega)
    simp only [conditional_145_57, source_145_57, target_145_57, hs, ht]

#print axioms conditional_context_145_57

theorem conditional_context_146_8 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 146 8 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_52 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 146 8 72 block_146_8.1
  · simpa only [block_146_8.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_139 (code/6) (by omega)
    have ht := conditional_at_123 (code%7776) (by omega)
    simp only [conditional_146_8, source_146_8, target_146_8, hs, ht]

#print axioms conditional_context_146_8

theorem conditional_context_146_57 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 146 57 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_52 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 146 57 72 block_146_57.1
  · simpa only [block_146_57.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_188 (code/6) (by omega)
    have ht := conditional_at_123 (code%7776) (by omega)
    simp only [conditional_146_57, source_146_57, target_146_57, hs, ht]

#print axioms conditional_context_146_57

theorem conditional_context_148_8 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 148 8 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_52 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 148 8 72 block_148_8.1
  · simpa only [block_148_8.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_139 (code/6) (by omega)
    have ht := conditional_at_125 (code%7776) (by omega)
    simp only [conditional_148_8, source_148_8, target_148_8, hs, ht]

#print axioms conditional_context_148_8

theorem conditional_context_148_57 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 148 57 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_52 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 148 57 72 block_148_57.1
  · simpa only [block_148_57.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_188 (code/6) (by omega)
    have ht := conditional_at_125 (code%7776) (by omega)
    simp only [conditional_148_57, source_148_57, target_148_57, hs, ht]

#print axioms conditional_context_148_57

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G177
