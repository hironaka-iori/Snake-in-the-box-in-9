import NatBoolean102
import BoundedPrefixTransfer102
import Context101Group02
import PotentialRoots102Group02
import PotentialRoots102Group03
import EmittingReduction101

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.BooleanComparison102.Ble
open Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem completed_prefix_99_37 :
    checkPrefix (fun code => Nat.ble
      (483+min 551 (value Completed.n5_57 (code%7776)))
      (120*(code%6+1)+max (if digit code 1 ≤ 2 ∧ digit code 2 ≤ 2 then 19 else 18) (if code%7776 = 3221 then 96 else 0)+min 551 (value Completed.n5_19 (code/6)))) 6 0 1807 = true := by decide +kernel

theorem completed_context_99_37 :
    contextCheck (weight completedCredit) 483 Completed.potential 99 37 = true := by
  apply contextCheck_of_bounded_prefix (fun code => Nat.ble
      (483+min 551 (value Completed.n5_57 (code%7776)))
      (120*(code%6+1)+max (if digit code 1 ≤ 2 ∧ digit code 2 ≤ 2 then 19 else 18) (if code%7776 = 3221 then 96 else 0)+min 551 (value Completed.n5_19 (code/6))))
    (weight completedCredit) 483 Completed.potential 99 37 12 block_99_37.1
  · simpa only [block_99_37.2] using completed_prefix_99_37
  · intro code hc _
    have hs := completed_at_168 (code/6) (by omega)
    have ht := completed_at_139 (code%7776) (by omega)
    simp only [Snake9.BooleanComparison102.ble_decide, completed_simplified_99_37, source_99_37, target_99_37, hs, ht]

#print axioms completed_prefix_99_37
#print axioms completed_context_99_37
end Snake9.BooleanComparison102.Ble
