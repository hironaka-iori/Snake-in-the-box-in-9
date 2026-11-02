import BoundedPrefixTransfer102
import Context101Group08
import JointTraversal103
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G462
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_174 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_91 (code/6)))) 6 0 3970 = true := by
  decide +kernel

theorem completed_context_352_65 :
    contextCheck (weight completedCredit) 483 Completed.potential 352 65 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_174 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 0)+min 551 (value Completed.n5_91 (code/6))))
    (weight completedCredit) 483 Completed.potential 352 65 124 block_352_65.1
  · simpa only [block_352_65.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_196 (code/6) (by omega)
    have ht := completed_at_200 (code%7776) (by omega)
    simp only [completed_352_65, source_352_65, target_352_65, hs, ht]

#print axioms completed_context_352_65

#print axioms prefix_checked
end Snake9.CompletedBatch104G462
