import BoundedPrefixTransfer102
import Context101Group03
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G182
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)) 496 602 6 0 3462
    Conditional.n5_62 Conditional.n5_64 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_64 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_62 (code/6)))) 6 0 3462 = true := by
  exact joint_root_prefix _ 496 602 3462 Conditional.n5_62 Conditional.n5_64 joint_checked

theorem conditional_context_150_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 150 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_64 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_62 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 150 0 59 block_150_0.1
  · simpa only [block_150_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_45 (code/6) (by omega)
    have ht := conditional_at_107 (code%7776) (by omega)
    simp only [conditional_150_0, source_150_0, target_150_0, hs, ht]

#print axioms conditional_context_150_0

theorem conditional_context_153_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 153 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_64 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_62 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 153 0 59 block_153_0.1
  · simpa only [block_153_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_45 (code/6) (by omega)
    have ht := conditional_at_111 (code%7776) (by omega)
    simp only [conditional_153_0, source_153_0, target_153_0, hs, ht]

#print axioms conditional_context_153_0

theorem conditional_context_165_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 165 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_64 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_62 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 165 0 59 block_165_0.1
  · simpa only [block_165_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_48 (code/6) (by omega)
    have ht := conditional_at_126 (code%7776) (by omega)
    simp only [conditional_165_0, source_165_0, target_165_0, hs, ht]

#print axioms conditional_context_165_0

theorem conditional_context_166_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 166 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_64 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_62 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 166 0 59 block_166_0.1
  · simpa only [block_166_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_48 (code/6) (by omega)
    have ht := conditional_at_127 (code%7776) (by omega)
    simp only [conditional_166_0, source_166_0, target_166_0, hs, ht]

#print axioms conditional_context_166_0

theorem conditional_context_169_0 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 169 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_64 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 16)+min 602 (value Conditional.n5_62 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 169 0 59 block_169_0.1
  · simpa only [block_169_0.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_48 (code/6) (by omega)
    have ht := conditional_at_131 (code%7776) (by omega)
    simp only [conditional_169_0, source_169_0, target_169_0, hs, ht]

#print axioms conditional_context_169_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G182
