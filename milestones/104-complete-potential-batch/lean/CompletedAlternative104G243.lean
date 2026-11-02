import BoundedPrefixTransfer102
import Context101Group04
import JointTraversal103
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G243
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)) 483 551 6 0 3772
    Completed.n5_158 Completed.n5_115 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_115 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_158 (code/6)))) 6 0 3772 = true := by
  exact joint_root_prefix _ 483 551 3772 Completed.n5_158 Completed.n5_115 joint_checked

theorem completed_context_181_52 :
    contextCheck (weight completedCredit) 483 Completed.potential 181 52 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_115 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_158 (code/6))))
    (weight completedCredit) 483 Completed.potential 181 52 90 block_181_52.1
  · simpa only [block_181_52.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_183 (code/6) (by omega)
    have ht := completed_at_189 (code%7776) (by omega)
    simp only [completed_181_52, source_181_52, target_181_52, hs, ht]

#print axioms completed_context_181_52

theorem completed_context_181_53 :
    contextCheck (weight completedCredit) 483 Completed.potential 181 53 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_115 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_158 (code/6))))
    (weight completedCredit) 483 Completed.potential 181 53 90 block_181_53.1
  · simpa only [block_181_53.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_184 (code/6) (by omega)
    have ht := completed_at_194 (code%7776) (by omega)
    simp only [completed_181_53, source_181_53, target_181_53, hs, ht]

#print axioms completed_context_181_53

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G243
