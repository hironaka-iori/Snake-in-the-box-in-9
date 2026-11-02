import BoundedPrefixTransfer102
import Context101Group01
import Context101Group02
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G104
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)) 496 602 6 0 2707
    Conditional.n5_58 Conditional.n5_37 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_58 (code/6)))) 6 0 2707 = true := by
  exact joint_root_prefix _ 496 602 2707 Conditional.n5_58 Conditional.n5_37 joint_checked

theorem conditional_context_80_32 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 80 32 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_58 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 80 32 32 block_80_32.1
  · simpa only [block_80_32.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_163 (code/6) (by omega)
    have ht := conditional_at_122 (code%7776) (by omega)
    simp only [conditional_80_32, source_80_32, target_80_32, hs, ht]

#print axioms conditional_context_80_32

theorem conditional_context_80_34 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 80 34 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_58 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 80 34 32 block_80_34.1
  · simpa only [block_80_34.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_165 (code/6) (by omega)
    have ht := conditional_at_122 (code%7776) (by omega)
    simp only [conditional_80_34, source_80_34, target_80_34, hs, ht]

#print axioms conditional_context_80_34

theorem conditional_context_81_32 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 81 32 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_58 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 81 32 32 block_81_32.1
  · simpa only [block_81_32.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_163 (code/6) (by omega)
    have ht := conditional_at_123 (code%7776) (by omega)
    simp only [conditional_81_32, source_81_32, target_81_32, hs, ht]

#print axioms conditional_context_81_32

theorem conditional_context_81_34 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 81 34 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_58 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 81 34 32 block_81_34.1
  · simpa only [block_81_34.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_165 (code/6) (by omega)
    have ht := conditional_at_123 (code%7776) (by omega)
    simp only [conditional_81_34, source_81_34, target_81_34, hs, ht]

#print axioms conditional_context_81_34

theorem conditional_context_82_32 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 82 32 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_58 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 82 32 32 block_82_32.1
  · simpa only [block_82_32.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_163 (code/6) (by omega)
    have ht := conditional_at_125 (code%7776) (by omega)
    simp only [conditional_82_32, source_82_32, target_82_32, hs, ht]

#print axioms conditional_context_82_32

theorem conditional_context_82_34 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 82 34 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_37 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 602 (value Conditional.n5_58 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 82 34 32 block_82_34.1
  · simpa only [block_82_34.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_165 (code/6) (by omega)
    have ht := conditional_at_125 (code%7776) (by omega)
    simp only [conditional_82_34, source_82_34, target_82_34, hs, ht]

#print axioms conditional_context_82_34

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G104
