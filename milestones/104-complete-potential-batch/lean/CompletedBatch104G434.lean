import BoundedPrefixTransfer102
import Context101Group08
import JointTraversal103
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G434
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_161 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [rule014] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_166 (code/6)))) 6 0 3960 = true := by
  decide +kernel

theorem completed_context_350_40 :
    contextCheck (weight completedCredit) 483 Completed.potential 350 40 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_161 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [rule014] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_166 (code/6))))
    (weight completedCredit) 483 Completed.potential 350 40 123 block_350_40.1
  · simpa only [block_350_40.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_171 (code/6) (by omega)
    have ht := completed_at_173 (code%7776) (by omega)
    simp only [completed_350_40, source_350_40, target_350_40, hs, ht]

#print axioms completed_context_350_40

#print axioms prefix_checked
end Snake9.CompletedBatch104G434
