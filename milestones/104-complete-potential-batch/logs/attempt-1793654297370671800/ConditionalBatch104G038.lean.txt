import BoundedPrefixTransfer102
import Context101Group00
import JointTraversal103
import PotentialRoots102Group02
import PotentialRoots102Group03

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.ConditionalBatch104G038
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem joint_checked : checkJoint (fun code => 120*(code%6+1)+max (max 0 (emittedCredit [rule036] code)) (max ((if code%7776 = 7106 then 96 else 0)) 18)) 496 602 6 0 2620
    Conditional.n5_49 Conditional.n5_71 = true := by decide +kernel

theorem prefix_checked : checkPrefix (fun code => decide
      (496+min 602 (value Conditional.n5_71 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [rule036] code)) (max ((if code%7776 = 7106 then 96 else 0)) 18)+min 602 (value Conditional.n5_49 (code/6)))) 6 0 2620 = true := by
  exact joint_root_prefix _ 496 602 2620 Conditional.n5_49 Conditional.n5_71 joint_checked

theorem conditional_context_35_60 :
    contextCheck (weight conditionalCredit) 496 Conditional.potential 35 60 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (496+min 602 (value Conditional.n5_71 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [rule036] code)) (max ((if code%7776 = 7106 then 96 else 0)) 18)+min 602 (value Conditional.n5_49 (code/6))))
    (weight conditionalCredit) 496 Conditional.potential 35 60 25 block_35_60.1
  · simpa only [block_35_60.2] using prefix_checked
  · intro code hc _
    have hs := conditional_at_191 (code/6) (by omega)
    have ht := conditional_at_135 (code%7776) (by omega)
    simp only [conditional_35_60, source_35_60, target_35_60, hs, ht]

#print axioms conditional_context_35_60

#print axioms prefix_checked
#print axioms joint_checked
end Snake9.ConditionalBatch104G038
