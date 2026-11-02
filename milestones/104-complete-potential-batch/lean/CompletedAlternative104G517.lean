import BoundedPrefixTransfer102
import Context101Group10
import Context101Group11
import Context101Group12
import JointTraversal103
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedAlternative104G517
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 0)) 483 551 6 0 3908
    Completed.n5_74 Completed.n5_54 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_54 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 0)+min 551 (value Completed.n5_74 (code/6)))) 6 0 3908 = true := by
  exact joint_root_prefix _ 483 551 3908 Completed.n5_74 Completed.n5_54 joint_checked

theorem completed_context_401_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 401 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_54 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 0)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 401 0 114 block_401_0.1
  · simpa only [block_401_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_111 (code/6) (by omega)
    have ht := completed_at_130 (code%7776) (by omega)
    simp only [completed_401_0, source_401_0, target_401_0, hs, ht]

#print axioms completed_context_401_0

theorem completed_context_473_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 473 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_54 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 0)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 473 0 114 block_473_0.1
  · simpa only [block_473_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_126 (code/6) (by omega)
    have ht := completed_at_130 (code%7776) (by omega)
    simp only [completed_473_0, source_473_0, target_473_0, hs, ht]

#print axioms completed_context_473_0

theorem completed_context_503_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 503 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_54 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max ((if code%7776 = 3221 then 96 else 0)) 0)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 503 0 114 block_503_0.1
  · simpa only [block_503_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_131 (code/6) (by omega)
    have ht := completed_at_130 (code%7776) (by omega)
    simp only [completed_503_0, source_503_0, target_503_0, hs, ht]

#print axioms completed_context_503_0

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.CompletedAlternative104G517
