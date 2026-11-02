import BoundedPrefixTransfer102
import Context101Group05
import Context101Group06
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G291
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_58 (code%7776)) ≤
        120*(code%6+1)+max (max 2 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_156 (code/6)))) 6 0 3823 = true := by
  decide +kernel

theorem conditional_context_215_1 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 215 1 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_58 (code%7776)) ≤
        120*(code%6+1)+max (max 2 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_156 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 215 1 101 block_215_1.1
  · simpa only [block_215_1.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_132 (code/6) (by omega)
    have ht := conditional_at_163 (code%7776) (by omega)
    simp only [conditional_215_1, source_215_1, target_215_1, hs, ht]

#print axioms conditional_context_215_1

theorem conditional_context_235_3 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 235 3 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_58 (code%7776)) ≤
        120*(code%6+1)+max (max 2 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 18)+min 602 (value Conditional.n5_156 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 235 3 101 block_235_3.1
  · simpa only [block_235_3.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_134 (code/6) (by omega)
    have ht := conditional_at_165 (code%7776) (by omega)
    simp only [conditional_235_3, source_235_3, target_235_3, hs, ht]

#print axioms conditional_context_235_3

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G291
