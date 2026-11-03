import BoundedPrefixTransfer102
import Context101Group01
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G083
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_76 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_115 (code/6)))) 6 0 2004 = true := by
  decide +kernel

theorem completed_context_71_58 :
    contextCheck (weight completedCredit) 483 Completed.potential 71 58 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_76 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_115 (code/6))))
    (weight completedCredit) 483 Completed.potential 71 58 14 block_71_58.1
  · simpa only [block_71_58.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_189 (code/6) (by omega)
    have ht := completed_at_109 (code%7776) (by omega)
    simp only [completed_71_58, source_71_58, target_71_58, hs, ht]

#print axioms completed_context_71_58

theorem completed_context_71_63 :
    contextCheck (weight completedCredit) 483 Completed.potential 71 63 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_76 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (0) 16)+min 551 (value Completed.n5_115 (code/6))))
    (weight completedCredit) 483 Completed.potential 71 63 14 block_71_63.1
  · simpa only [block_71_63.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_194 (code/6) (by omega)
    have ht := completed_at_109 (code%7776) (by omega)
    simp only [completed_71_63, source_71_63, target_71_63, hs, ht]

#print axioms completed_context_71_63

#print axioms prefix_checked
end Snake9.CompletedBatch104G083
