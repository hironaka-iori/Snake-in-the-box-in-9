import BoundedPrefixTransfer102
import Context101Group00
import PotentialRoots102Group00

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.PrefixCertificates102
open Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem completed_prefix_10_0 :
    checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_112 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_120 (code/6)))) 6 0 1378 = true := by decide +kernel

theorem completed_context_10_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 10 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_112 (code%7776)) ≤
        120*(code%6+1)+max (max 12 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_120 (code/6))))
    (weight completedCredit) 483 Completed.potential 10 0 8 block_10_0.1
  · simpa only [block_10_0.2] using completed_prefix_10_0
  · intro code hc _
    have hs := completed_at_2 (code/6) (by omega)
    have ht := completed_at_36 (code%7776) (by omega)
    simp only [completed_10_0, source_10_0, target_10_0, hs, ht]

#print axioms completed_prefix_10_0
#print axioms completed_context_10_0
end Snake9.PrefixCertificates102
