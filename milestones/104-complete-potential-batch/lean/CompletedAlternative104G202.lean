import BoundedPrefixTransfer102
import Context101Group04
import JointTraversal103
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G202
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 5 (emittedCredit [rule013] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)) 483 551 6 0 3532
    Completed.n5_144 Completed.n5_52 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_52 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [rule013] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_144 (code/6)))) 6 0 3532 = true := by
  exact joint_root_prefix _ 483 551 3532 Completed.n5_144 Completed.n5_52 joint_checked

theorem completed_context_172_36 :
    contextCheck (weight completedCredit) 483 Completed.potential 172 36 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_52 (code%7776)) ≤
        120*(code%6+1)+max (max 5 (emittedCredit [rule013] code)) (max ((if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0)) 16)+min 551 (value Completed.n5_144 (code/6))))
    (weight completedCredit) 483 Completed.potential 172 36 78 block_172_36.1
  · simpa only [block_172_36.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_167 (code/6) (by omega)
    have ht := completed_at_192 (code%7776) (by omega)
    simp only [completed_172_36, source_172_36, target_172_36, hs, ht]

#print axioms completed_context_172_36

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G202
