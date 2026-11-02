import BoundedPrefixTransfer102
import Context101Group02
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalAlternative104G105
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_105 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_74 (code/6)))) 6 0 2711 = true := by
  decide +kernel

theorem conditional_context_83_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 83 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_105 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_74 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 83 0 33 block_83_0.1
  · simpa only [block_83_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_24 (code/6) (by omega)
    have ht := conditional_at_128 (code%7776) (by omega)
    simp only [conditional_83_0, source_83_0, target_83_0, hs, ht]

#print axioms conditional_context_83_0

#print axioms prefix_checked
end Snake9.ConditionalAlternative104G105
