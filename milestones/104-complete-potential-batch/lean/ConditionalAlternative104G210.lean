import BoundedPrefixTransfer102
import Context101Group04
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G210
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_135 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_158 (code/6)))) 6 0 3579 = true := by
  decide +kernel

theorem conditional_context_176_70 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 176 70 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_135 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_158 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 176 70 83 block_176_70.1
  · simpa only [block_176_70.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_201 (code/6) (by omega)
    have ht := conditional_at_18 (code%7776) (by omega)
    simp only [conditional_176_70, source_176_70, target_176_70, hs, ht]

#print axioms conditional_context_176_70

theorem conditional_context_176_72 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 176 72 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_135 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_158 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 176 72 83 block_176_72.1
  · simpa only [block_176_72.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_203 (code/6) (by omega)
    have ht := conditional_at_18 (code%7776) (by omega)
    simp only [conditional_176_72, source_176_72, target_176_72, hs, ht]

#print axioms conditional_context_176_72

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G210
