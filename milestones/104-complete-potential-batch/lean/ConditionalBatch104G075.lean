import BoundedPrefixTransfer102
import Context101Group01
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G075
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)) 496 602 6 0 2626
    Conditional.n5_76 Conditional.n5_124 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_124 (code%7776)) ≤
        120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_76 (code/6)))) 6 0 2626 = true := by
  exact joint_root_prefix _ 496 602 2626 Conditional.n5_76 Conditional.n5_124 joint_checked

theorem conditional_context_64_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 64 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_124 (code%7776)) ≤
        120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_76 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 64 0 26 block_64_0.1
  · simpa only [block_64_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_20 (code/6) (by omega)
    have ht := conditional_at_117 (code%7776) (by omega)
    simp only [conditional_64_0, source_64_0, target_64_0, hs, ht]

#print axioms conditional_context_64_0

theorem conditional_context_65_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 65 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_124 (code%7776)) ≤
        120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_76 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 65 0 26 block_65_0.1
  · simpa only [block_65_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_20 (code/6) (by omega)
    have ht := conditional_at_118 (code%7776) (by omega)
    simp only [conditional_65_0, source_65_0, target_65_0, hs, ht]

#print axioms conditional_context_65_0

theorem conditional_context_68_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 68 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_124 (code%7776)) ≤
        120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_76 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 68 0 26 block_68_0.1
  · simpa only [block_68_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_20 (code/6) (by omega)
    have ht := conditional_at_121 (code%7776) (by omega)
    simp only [conditional_68_0, source_68_0, target_68_0, hs, ht]

#print axioms conditional_context_68_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G075
