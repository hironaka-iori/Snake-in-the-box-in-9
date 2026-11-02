import BoundedPrefixTransfer102
import Context101Group01
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G081
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_64 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_87 (code/6)))) 6 0 2715 = true := by
  decide +kernel

theorem conditional_context_70_58 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 70 58 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_64 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_87 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 70 58 34 block_70_58.1
  · simpa only [block_70_58.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_189 (code/6) (by omega)
    have ht := conditional_at_107 (code%7776) (by omega)
    simp only [conditional_70_58, source_70_58, target_70_58, hs, ht]

#print axioms conditional_context_70_58

theorem conditional_context_70_63 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 70 63 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_64 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_87 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 70 63 34 block_70_63.1
  · simpa only [block_70_63.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_194 (code/6) (by omega)
    have ht := conditional_at_107 (code%7776) (by omega)
    simp only [conditional_70_63, source_70_63, target_70_63, hs, ht]

#print axioms conditional_context_70_63

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G081
