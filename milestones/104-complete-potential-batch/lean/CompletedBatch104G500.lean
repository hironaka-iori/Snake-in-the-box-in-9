import BoundedPrefixTransfer102
import Context101Group09
import Context101Group10
import Context101Group11
import Context101Group12
import JointTraversal103
import PotentialRoots102Group02

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Snake9.CompletedBatch104G500
open Snake9.Joint103 Snake9.PrefixChecker100 Snake9.BoundedPrefixTransfer102 Snake9.PotentialChecker99
open Snake9.Potential99 Snake9.PotentialBlocks102 Snake9.Context101
open Snake9.Weights98 Snake9.CountFree98 Snake9.GraphWalk78 Snake9.Batch92
open Snake9.ContextWeights101 Snake9.ConcreteCatalogue95 Snake9.Guards79

theorem prefix_checked : checkPrefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6)))) 6 0 2715 = true := by
  decide +kernel

theorem completed_context_378_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 378 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 378 0 34 block_378_0.1
  · simpa only [block_378_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_107 (code/6) (by omega)
    have ht := completed_at_107 (code%7776) (by omega)
    simp only [completed_378_0, source_378_0, target_378_0, hs, ht]

#print axioms completed_context_378_0

theorem completed_context_382_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 382 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 382 0 34 block_382_0.1
  · simpa only [block_382_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_107 (code/6) (by omega)
    have ht := completed_at_111 (code%7776) (by omega)
    simp only [completed_382_0, source_382_0, target_382_0, hs, ht]

#print axioms completed_context_382_0

theorem completed_context_397_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 397 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 397 0 34 block_397_0.1
  · simpa only [block_397_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_111 (code/6) (by omega)
    have ht := completed_at_126 (code%7776) (by omega)
    simp only [completed_397_0, source_397_0, target_397_0, hs, ht]

#print axioms completed_context_397_0

theorem completed_context_398_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 398 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 398 0 34 block_398_0.1
  · simpa only [block_398_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_111 (code/6) (by omega)
    have ht := completed_at_127 (code%7776) (by omega)
    simp only [completed_398_0, source_398_0, target_398_0, hs, ht]

#print axioms completed_context_398_0

theorem completed_context_402_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 402 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 402 0 34 block_402_0.1
  · simpa only [block_402_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_111 (code/6) (by omega)
    have ht := completed_at_131 (code%7776) (by omega)
    simp only [completed_402_0, source_402_0, target_402_0, hs, ht]

#print axioms completed_context_402_0

theorem completed_context_469_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 469 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 469 0 34 block_469_0.1
  · simpa only [block_469_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_126 (code/6) (by omega)
    have ht := completed_at_126 (code%7776) (by omega)
    simp only [completed_469_0, source_469_0, target_469_0, hs, ht]

#print axioms completed_context_469_0

theorem completed_context_470_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 470 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 470 0 34 block_470_0.1
  · simpa only [block_470_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_126 (code/6) (by omega)
    have ht := completed_at_127 (code%7776) (by omega)
    simp only [completed_470_0, source_470_0, target_470_0, hs, ht]

#print axioms completed_context_470_0

theorem completed_context_474_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 474 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 474 0 34 block_474_0.1
  · simpa only [block_474_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_126 (code/6) (by omega)
    have ht := completed_at_131 (code%7776) (by omega)
    simp only [completed_474_0, source_474_0, target_474_0, hs, ht]

#print axioms completed_context_474_0

theorem completed_context_475_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 475 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 475 0 34 block_475_0.1
  · simpa only [block_475_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_127 (code/6) (by omega)
    have ht := completed_at_111 (code%7776) (by omega)
    simp only [completed_475_0, source_475_0, target_475_0, hs, ht]

#print axioms completed_context_475_0

theorem completed_context_476_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 476 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 476 0 34 block_476_0.1
  · simpa only [block_476_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_127 (code/6) (by omega)
    have ht := completed_at_107 (code%7776) (by omega)
    simp only [completed_476_0, source_476_0, target_476_0, hs, ht]

#print axioms completed_context_476_0

theorem completed_context_480_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 480 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 480 0 34 block_480_0.1
  · simpa only [block_480_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_127 (code/6) (by omega)
    have ht := completed_at_111 (code%7776) (by omega)
    simp only [completed_480_0, source_480_0, target_480_0, hs, ht]

#print axioms completed_context_480_0

theorem completed_context_498_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 498 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 498 0 34 block_498_0.1
  · simpa only [block_498_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_131 (code/6) (by omega)
    have ht := completed_at_131 (code%7776) (by omega)
    simp only [completed_498_0, source_498_0, target_498_0, hs, ht]

#print axioms completed_context_498_0

theorem completed_context_499_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 499 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 499 0 34 block_499_0.1
  · simpa only [block_499_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_131 (code/6) (by omega)
    have ht := completed_at_126 (code%7776) (by omega)
    simp only [completed_499_0, source_499_0, target_499_0, hs, ht]

#print axioms completed_context_499_0

theorem completed_context_500_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 500 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 500 0 34 block_500_0.1
  · simpa only [block_500_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_131 (code/6) (by omega)
    have ht := completed_at_127 (code%7776) (by omega)
    simp only [completed_500_0, source_500_0, target_500_0, hs, ht]

#print axioms completed_context_500_0

theorem completed_context_504_0 :
    contextCheck (weight completedCredit) 483 Completed.potential 504 0 = true := by
  apply contextCheck_of_bounded_prefix (fun code => decide
      (483+min 551 (value Completed.n5_74 (code%7776)) ≤
        120*(code%6+1)+max (max 0 (emittedCredit [] code)) (max (max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0)))) 12)+min 551 (value Completed.n5_74 (code/6))))
    (weight completedCredit) 483 Completed.potential 504 0 34 block_504_0.1
  · simpa only [block_504_0.2] using prefix_checked
  · intro code hc _
    have hs := completed_at_131 (code/6) (by omega)
    have ht := completed_at_131 (code%7776) (by omega)
    simp only [completed_504_0, source_504_0, target_504_0, hs, ht]

#print axioms completed_context_504_0

#print axioms prefix_checked
end Snake9.CompletedBatch104G500
