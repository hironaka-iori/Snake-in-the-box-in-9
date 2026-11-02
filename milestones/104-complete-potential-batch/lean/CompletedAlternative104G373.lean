import BoundedPrefixTransfer102
import Context101Group07
import JointTraversal103
import PotentialRoots102Group00
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G373
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)) 483 551 6 0 3835
    Completed.n5_3 Completed.n5_16 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_16 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_3 (code/6)))) 6 0 3835 = true := by
  exact joint_root_prefix _ 483 551 3835 Completed.n5_3 Completed.n5_16 joint_checked

theorem completed_context_300_39 :
    contextCheck (weight completedCredit) 483 Completed.potential 300 39 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_16 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_3 (code/6))))
    (weight completedCredit) 483 Completed.potential 300 39 103 block_300_39.1
  · simpa only [block_300_39.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_170 (code/6) (by omega)
    have ht := completed_at_28 (code%7776) (by omega)
    simp only [completed_300_39, source_300_39, target_300_39, hs, ht]

#print axioms completed_context_300_39

theorem completed_context_301_38 :
    contextCheck (weight completedCredit) 483 Completed.potential 301 38 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_16 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_3 (code/6))))
    (weight completedCredit) 483 Completed.potential 301 38 103 block_301_38.1
  · simpa only [block_301_38.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_169 (code/6) (by omega)
    have ht := completed_at_28 (code%7776) (by omega)
    simp only [completed_301_38, source_301_38, target_301_38, hs, ht]

#print axioms completed_context_301_38

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G373
