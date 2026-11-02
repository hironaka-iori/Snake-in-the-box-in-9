import BoundedPrefixTransfer102
import Context101Group02
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G132
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)) 496 602 6 0 1878
    Conditional.n5_17 Conditional.n5_62 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_62 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_17 (code/6)))) 6 0 1878 = true := by
  exact joint_root_prefix _ 496 602 1878 Conditional.n5_17 Conditional.n5_62 joint_checked

theorem conditional_context_100_37 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 100 37 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_62 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_17 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 100 37 13 block_100_37.1
  · simpa only [block_100_37.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_168 (code/6) (by omega)
    have ht := conditional_at_45 (code%7776) (by omega)
    simp only [conditional_100_37, source_100_37, target_100_37, hs, ht]

#print axioms conditional_context_100_37

theorem conditional_context_102_37 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 102 37 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_62 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_17 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 102 37 13 block_102_37.1
  · simpa only [block_102_37.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_168 (code/6) (by omega)
    have ht := conditional_at_48 (code%7776) (by omega)
    simp only [conditional_102_37, source_102_37, target_102_37, hs, ht]

#print axioms conditional_context_102_37

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G132
