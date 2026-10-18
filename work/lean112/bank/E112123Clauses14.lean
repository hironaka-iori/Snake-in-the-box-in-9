import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 30 = true ∨ valuationOf q 812 = true := by
  have hs : count811 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (812)) (countLit q [-29]) (countLit q [-30]) (count811 q) 1 1 (meaningNeg29 q) (meaningNeg30 q) (meaning812 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 30 = true ∨ valuation q 812 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 814 = true := by
  have hs : count813 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (812)) (literal (valuationOf q) (814)) (countLit q [-27]) (countLit q [-29, -30]) (count813 q) 2 (meaning812 q) (meaning814 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 814 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 812 = false ∨ valuationOf q 815 = true := by
  have hs : count813 q = (countLit q [-27]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -30])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (812)) (literal (valuationOf q) (815)) (countLit q [-27]) (countLit q [-29, -30]) (count813 q) 1 2 (meaningNeg27 q) (meaning812 q) (meaning815 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 812 = false ∨ valuationOf q 815 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 812 = false ∨ valuation q 815 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 816 = true := by
  have hs : count816 q = (countLit q [-32]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (816)) (countLit q [-32]) (countLit q [-33]) (count816 q) 1 (meaningNeg33 q) (meaning816 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 816 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 816 = true := by
  have hs : count816 q = (countLit q [-32]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (816)) (countLit q [-32]) (countLit q [-33]) (count816 q) 1 (meaningNeg32 q) (meaning816 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 816 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 33 = true ∨ valuationOf q 817 = true := by
  have hs : count816 q = (countLit q [-32]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (817)) (countLit q [-32]) (countLit q [-33]) (count816 q) 1 1 (meaningNeg32 q) (meaningNeg33 q) (meaning817 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 33 = true ∨ valuation q 817 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 818 = true := by
  have hs : count818 q = (countLit q [-36]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (818)) (countLit q [-36]) (countLit q [-39]) (count818 q) 1 (meaningNeg36 q) (meaning818 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 818 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 818 = false ∨ valuationOf q 820 = true := by
  have hs : count820 q = (countLit q [-32, -33]) + (countLit q [-36, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -33]) (l₂ := [-36, -39])
  have hm := merge_right (literal (valuationOf q) (818)) (literal (valuationOf q) (820)) (countLit q [-32, -33]) (countLit q [-36, -39]) (count820 q) 1 (meaning818 q) (meaning820 q) hs
  change valuationOf q 818 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 818 = false ∨ valuation q 820 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 820 = true := by
  have hs : count820 q = (countLit q [-32, -33]) + (countLit q [-36, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -33]) (l₂ := [-36, -39])
  have hm := merge_left (literal (valuationOf q) (816)) (literal (valuationOf q) (820)) (countLit q [-32, -33]) (countLit q [-36, -39]) (count820 q) 1 (meaning816 q) (meaning820 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 820 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 818 = false ∨ valuationOf q 821 = true := by
  have hs : count820 q = (countLit q [-32, -33]) + (countLit q [-36, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -33]) (l₂ := [-36, -39])
  have hm := merge_two (literal (valuationOf q) (816)) (literal (valuationOf q) (818)) (literal (valuationOf q) (821)) (countLit q [-32, -33]) (countLit q [-36, -39]) (count820 q) 1 1 (meaning816 q) (meaning818 q) (meaning821 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 818 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 818 = false ∨ valuation q 821 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 821 = true := by
  have hs : count820 q = (countLit q [-32, -33]) + (countLit q [-36, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -33]) (l₂ := [-36, -39])
  have hm := merge_left (literal (valuationOf q) (817)) (literal (valuationOf q) (821)) (countLit q [-32, -33]) (countLit q [-36, -39]) (count820 q) 2 (meaning817 q) (meaning821 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 821 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 825 = true := by
  have hs : count824 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -33, -36, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -33, -36, -39])
  have hm := merge_left (literal (valuationOf q) (814)) (literal (valuationOf q) (825)) (countLit q [-27, -29, -30]) (countLit q [-32, -33, -36, -39]) (count824 q) 2 (meaning814 q) (meaning825 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 825 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 820 = false ∨ valuationOf q 826 = true := by
  have hs : count824 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -33, -36, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -33, -36, -39])
  have hm := merge_two (literal (valuationOf q) (814)) (literal (valuationOf q) (820)) (literal (valuationOf q) (826)) (countLit q [-27, -29, -30]) (countLit q [-32, -33, -36, -39]) (count824 q) 2 1 (meaning814 q) (meaning820 q) (meaning826 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 820 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 820 = false ∨ valuation q 826 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 821 = false ∨ valuationOf q 827 = true := by
  have hs : count824 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -33, -36, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -33, -36, -39])
  have hm := merge_two (literal (valuationOf q) (814)) (literal (valuationOf q) (821)) (literal (valuationOf q) (827)) (countLit q [-27, -29, -30]) (countLit q [-32, -33, -36, -39]) (count824 q) 2 2 (meaning814 q) (meaning821 q) (meaning827 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 821 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 821 = false ∨ valuation q 827 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 826 = true := by
  have hs : count824 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -33, -36, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -33, -36, -39])
  have hm := merge_left (literal (valuationOf q) (815)) (literal (valuationOf q) (826)) (countLit q [-27, -29, -30]) (countLit q [-32, -33, -36, -39]) (count824 q) 3 (meaning815 q) (meaning826 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 826 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 820 = false ∨ valuationOf q 827 = true := by
  have hs : count824 q = (countLit q [-27, -29, -30]) + (countLit q [-32, -33, -36, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30]) (l₂ := [-32, -33, -36, -39])
  have hm := merge_two (literal (valuationOf q) (815)) (literal (valuationOf q) (820)) (literal (valuationOf q) (827)) (countLit q [-27, -29, -30]) (countLit q [-32, -33, -36, -39]) (count824 q) 3 1 (meaning815 q) (meaning820 q) (meaning827 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 820 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 820 = false ∨ valuation q 827 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 831 = true := by
  have hs : count831 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (831)) (countLit q [-42]) (countLit q [-45]) (count831 q) 1 (meaningNeg45 q) (meaning831 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 831 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 831 = true := by
  have hs : count831 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (831)) (countLit q [-42]) (countLit q [-45]) (count831 q) 1 (meaningNeg42 q) (meaning831 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 831 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 45 = true ∨ valuationOf q 832 = true := by
  have hs : count831 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (832)) (countLit q [-42]) (countLit q [-45]) (count831 q) 1 1 (meaningNeg42 q) (meaningNeg45 q) (meaning832 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 45 = true ∨ valuation q 832 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 831 = false ∨ valuationOf q 833 = true := by
  have hs : count833 q = (countLit q [-41]) + (countLit q [-42, -45]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -45])
  have hm := merge_right (literal (valuationOf q) (831)) (literal (valuationOf q) (833)) (countLit q [-41]) (countLit q [-42, -45]) (count833 q) 1 (meaning831 q) (meaning833 q) hs
  change valuationOf q 831 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 831 = false ∨ valuation q 833 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 832 = false ∨ valuationOf q 834 = true := by
  have hs : count833 q = (countLit q [-41]) + (countLit q [-42, -45]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -45])
  have hm := merge_right (literal (valuationOf q) (832)) (literal (valuationOf q) (834)) (countLit q [-41]) (countLit q [-42, -45]) (count833 q) 2 (meaning832 q) (meaning834 q) hs
  change valuationOf q 832 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 832 = false ∨ valuation q 834 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 833 = true := by
  have hs : count833 q = (countLit q [-41]) + (countLit q [-42, -45]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -45])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (833)) (countLit q [-41]) (countLit q [-42, -45]) (count833 q) 1 (meaningNeg41 q) (meaning833 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 833 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 831 = false ∨ valuationOf q 834 = true := by
  have hs : count833 q = (countLit q [-41]) + (countLit q [-42, -45]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -45])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (831)) (literal (valuationOf q) (834)) (countLit q [-41]) (countLit q [-42, -45]) (count833 q) 1 1 (meaningNeg41 q) (meaning831 q) (meaning834 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 831 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 831 = false ∨ valuation q 834 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 836 = true := by
  have hs : count836 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (836)) (countLit q [-47]) (countLit q [-48]) (count836 q) 1 (meaningNeg48 q) (meaning836 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 836 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 836 = true := by
  have hs : count836 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (836)) (countLit q [-47]) (countLit q [-48]) (count836 q) 1 (meaningNeg47 q) (meaning836 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 836 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 836 = false ∨ valuationOf q 840 = true := by
  have hs : count840 q = (countLit q [-47, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-47, -48]) (l₂ := [-50, -51])
  have hm := merge_left (literal (valuationOf q) (836)) (literal (valuationOf q) (840)) (countLit q [-47, -48]) (countLit q [-50, -51]) (count840 q) 1 (meaning836 q) (meaning840 q) hs
  change valuationOf q 836 = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 836 = false ∨ valuation q 840 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 844 = true := by
  have hs : count844 q = (countLit q [-41, -42, -45]) + (countLit q [-47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -45]) (l₂ := [-47, -48, -50, -51])
  have hm := merge_right (literal (valuationOf q) (840)) (literal (valuationOf q) (844)) (countLit q [-41, -42, -45]) (countLit q [-47, -48, -50, -51]) (count844 q) 1 (meaning840 q) (meaning844 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 844 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 833 = false ∨ valuationOf q 844 = true := by
  have hs : count844 q = (countLit q [-41, -42, -45]) + (countLit q [-47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -45]) (l₂ := [-47, -48, -50, -51])
  have hm := merge_left (literal (valuationOf q) (833)) (literal (valuationOf q) (844)) (countLit q [-41, -42, -45]) (countLit q [-47, -48, -50, -51]) (count844 q) 1 (meaning833 q) (meaning844 q) hs
  change valuationOf q 833 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 833 = false ∨ valuation q 844 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 834 = false ∨ valuationOf q 845 = true := by
  have hs : count844 q = (countLit q [-41, -42, -45]) + (countLit q [-47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -45]) (l₂ := [-47, -48, -50, -51])
  have hm := merge_left (literal (valuationOf q) (834)) (literal (valuationOf q) (845)) (countLit q [-41, -42, -45]) (countLit q [-47, -48, -50, -51]) (count844 q) 2 (meaning834 q) (meaning845 q) hs
  change valuationOf q 834 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 834 = false ∨ valuation q 845 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 852 = true := by
  have hs : count851 q = (countLit q [-27, -29, -30, -32, -33, -36, -39]) + (countLit q [-41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -33, -36, -39]) (l₂ := [-41, -42, -45, -47, -48, -50, -51])
  have hm := merge_left (literal (valuationOf q) (825)) (literal (valuationOf q) (852)) (countLit q [-27, -29, -30, -32, -33, -36, -39]) (countLit q [-41, -42, -45, -47, -48, -50, -51]) (count851 q) 2 (meaning825 q) (meaning852 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 852 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 844 = false ∨ valuationOf q 853 = true := by
  have hs : count851 q = (countLit q [-27, -29, -30, -32, -33, -36, -39]) + (countLit q [-41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -33, -36, -39]) (l₂ := [-41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (825)) (literal (valuationOf q) (844)) (literal (valuationOf q) (853)) (countLit q [-27, -29, -30, -32, -33, -36, -39]) (countLit q [-41, -42, -45, -47, -48, -50, -51]) (count851 q) 2 1 (meaning825 q) (meaning844 q) (meaning853 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 844 = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 844 = false ∨ valuation q 853 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 845 = false ∨ valuationOf q 854 = true := by
  have hs : count851 q = (countLit q [-27, -29, -30, -32, -33, -36, -39]) + (countLit q [-41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -33, -36, -39]) (l₂ := [-41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (825)) (literal (valuationOf q) (845)) (literal (valuationOf q) (854)) (countLit q [-27, -29, -30, -32, -33, -36, -39]) (countLit q [-41, -42, -45, -47, -48, -50, -51]) (count851 q) 2 2 (meaning825 q) (meaning845 q) (meaning854 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 845 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 845 = false ∨ valuation q 854 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E123.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112123
