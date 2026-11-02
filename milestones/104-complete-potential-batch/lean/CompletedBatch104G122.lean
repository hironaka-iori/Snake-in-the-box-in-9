import BoundedPrefixTransfer102
import Context101Group02
import JointTraversal103
import PotentialRoots102Group00

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G122
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_141 (code%7776)) ≤
        120*(code%6+1)+max (max 22 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_17 (code/6)))) 6 0 669 = true := by
  decide +kernel

theorem completed_context_96_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 96 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_141 (code%7776)) ≤
        120*(code%6+1)+max (max 22 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_17 (code/6))))
    (weight completedCredit) 483 Completed.potential 96 0 3 block_96_0.1
  · simpa only [block_96_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_27 (code/6) (by omega)
    have ht := completed_at_37 (code%7776) (by omega)
    simp only [completed_96_0, source_96_0, target_96_0, hs, ht]

#print axioms completed_context_96_0

#print axioms prefix_checked
end Snake9.CompletedBatch104G122
