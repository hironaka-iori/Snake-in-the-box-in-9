import BoundedPrefixTransfer102
import Context101Group09
import Context101Group12
import JointTraversal103
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G501
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)) 496 602 6 0 3456
    Conditional.n5_67 Conditional.n5_124 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_124 (code%7776)) ≤
        120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_67 (code/6)))) 6 0 3456 = true := by
  exact joint_root_prefix _ 496 602 3456 Conditional.n5_67 Conditional.n5_124 joint_checked

theorem conditional_context_388_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 388 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_124 (code%7776)) ≤
        120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_67 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 388 0 57 block_388_0.1
  · simpa only [block_388_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_109 (code/6) (by omega)
    have ht := conditional_at_117 (code%7776) (by omega)
    simp only [conditional_388_0, source_388_0, target_388_0, hs, ht]

#print axioms conditional_context_388_0

theorem conditional_context_389_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 389 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_124 (code%7776)) ≤
        120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_67 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 389 0 57 block_389_0.1
  · simpa only [block_389_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_109 (code/6) (by omega)
    have ht := conditional_at_118 (code%7776) (by omega)
    simp only [conditional_389_0, source_389_0, target_389_0, hs, ht]

#print axioms conditional_context_389_0

theorem conditional_context_392_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 392 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_124 (code%7776)) ≤
        120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_67 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 392 0 57 block_392_0.1
  · simpa only [block_392_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_109 (code/6) (by omega)
    have ht := conditional_at_121 (code%7776) (by omega)
    simp only [conditional_392_0, source_392_0, target_392_0, hs, ht]

#print axioms conditional_context_392_0

theorem conditional_context_487_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 487 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_124 (code%7776)) ≤
        120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_67 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 487 0 57 block_487_0.1
  · simpa only [block_487_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_129 (code/6) (by omega)
    have ht := conditional_at_121 (code%7776) (by omega)
    simp only [conditional_487_0, source_487_0, target_487_0, hs, ht]

#print axioms conditional_context_487_0

theorem conditional_context_488_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 488 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_124 (code%7776)) ≤
        120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_67 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 488 0 57 block_488_0.1
  · simpa only [block_488_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_129 (code/6) (by omega)
    have ht := conditional_at_117 (code%7776) (by omega)
    simp only [conditional_488_0, source_488_0, target_488_0, hs, ht]

#print axioms conditional_context_488_0

theorem conditional_context_489_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 489 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_124 (code%7776)) ≤
        120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_67 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 489 0 57 block_489_0.1
  · simpa only [block_489_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_129 (code/6) (by omega)
    have ht := conditional_at_118 (code%7776) (by omega)
    simp only [conditional_489_0, source_489_0, target_489_0, hs, ht]

#print axioms conditional_context_489_0

theorem conditional_context_492_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 492 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_124 (code%7776)) ≤
        120*(code%6+1)+max (max 18 (emittedCredit [] code)) (max (0) 16)+min 602 (value Conditional.n5_67 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 492 0 57 block_492_0.1
  · simpa only [block_492_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_129 (code/6) (by omega)
    have ht := conditional_at_121 (code%7776) (by omega)
    simp only [conditional_492_0, source_492_0, target_492_0, hs, ht]

#print axioms conditional_context_492_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G501
