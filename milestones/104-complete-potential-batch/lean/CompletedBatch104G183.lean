import BoundedPrefixTransfer102
import Context101Group03
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G183
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_79 (code/6)))) 6 0 3462 = true := by
  decide +kernel

theorem completed_context_150_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 150 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_79 (code/6))))
    (weight completedCredit) 483 Completed.potential 150 0 59 block_150_0.1
  · simpa only [block_150_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_45 (code/6) (by omega)
    have ht := completed_at_107 (code%7776) (by omega)
    simp only [completed_150_0, source_150_0, target_150_0, hs, ht]

#print axioms completed_context_150_0

theorem completed_context_153_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 153 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_79 (code/6))))
    (weight completedCredit) 483 Completed.potential 153 0 59 block_153_0.1
  · simpa only [block_153_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_45 (code/6) (by omega)
    have ht := completed_at_111 (code%7776) (by omega)
    simp only [completed_153_0, source_153_0, target_153_0, hs, ht]

#print axioms completed_context_153_0

theorem completed_context_165_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 165 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_79 (code/6))))
    (weight completedCredit) 483 Completed.potential 165 0 59 block_165_0.1
  · simpa only [block_165_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_48 (code/6) (by omega)
    have ht := completed_at_126 (code%7776) (by omega)
    simp only [completed_165_0, source_165_0, target_165_0, hs, ht]

#print axioms completed_context_165_0

theorem completed_context_166_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 166 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_79 (code/6))))
    (weight completedCredit) 483 Completed.potential 166 0 59 block_166_0.1
  · simpa only [block_166_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_48 (code/6) (by omega)
    have ht := completed_at_127 (code%7776) (by omega)
    simp only [completed_166_0, source_166_0, target_166_0, hs, ht]

#print axioms completed_context_166_0

theorem completed_context_169_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 169 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_79 (code/6))))
    (weight completedCredit) 483 Completed.potential 169 0 59 block_169_0.1
  · simpa only [block_169_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_48 (code/6) (by omega)
    have ht := completed_at_131 (code%7776) (by omega)
    simp only [completed_169_0, source_169_0, target_169_0, hs, ht]

#print axioms completed_context_169_0

#print axioms prefix_checked
end Snake9.CompletedBatch104G183
