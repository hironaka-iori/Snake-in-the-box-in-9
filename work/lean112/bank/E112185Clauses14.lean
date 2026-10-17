import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 748 = true := by
  have hs : count748 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_right (literal (valuationOf q) (-9)) (literal (valuationOf q) (748)) (countLit q [-6]) (countLit q [-9]) (count748 q) 1 (meaningNeg9 q) (meaning748 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 748 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 748 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 748 = true := by
  have hs : count748 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (748)) (countLit q [-6]) (countLit q [-9]) (count748 q) 1 (meaningNeg6 q) (meaning748 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 748 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 748 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 9 = true ∨ valuationOf q 749 = true := by
  have hs : count748 q = (countLit q [-6]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-9])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-9)) (literal (valuationOf q) (749)) (countLit q [-6]) (countLit q [-9]) (count748 q) 1 1 (meaningNeg6 q) (meaningNeg9 q) (meaning749 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 9)) = false ∨ valuationOf q 749 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 9 = true ∨ valuation q 749 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 750 = true := by
  have hs : count750 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (750)) (countLit q [-11]) (countLit q [-12]) (count750 q) 1 (meaningNeg12 q) (meaning750 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 750 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 750 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 750 = true := by
  have hs : count750 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (750)) (countLit q [-11]) (countLit q [-12]) (count750 q) 1 (meaningNeg11 q) (meaning750 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 750 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 750 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 12 = true ∨ valuationOf q 751 = true := by
  have hs : count750 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (751)) (countLit q [-11]) (countLit q [-12]) (count750 q) 1 1 (meaningNeg11 q) (meaningNeg12 q) (meaning751 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 751 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 12 = true ∨ valuation q 751 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 750 = false ∨ valuationOf q 752 = true := by
  have hs : count752 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (750)) (literal (valuationOf q) (752)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count752 q) 1 (meaning750 q) (meaning752 q) hs
  change valuationOf q 750 = false ∨ valuationOf q 752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 750 = false ∨ valuation q 752 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 751 = false ∨ valuationOf q 753 = true := by
  have hs : count752 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (751)) (literal (valuationOf q) (753)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count752 q) 2 (meaning751 q) (meaning753 q) hs
  change valuationOf q 751 = false ∨ valuationOf q 753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 751 = false ∨ valuation q 753 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 748 = false ∨ valuationOf q 752 = true := by
  have hs : count752 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_left (literal (valuationOf q) (748)) (literal (valuationOf q) (752)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count752 q) 1 (meaning748 q) (meaning752 q) hs
  change valuationOf q 748 = false ∨ valuationOf q 752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 748 = false ∨ valuation q 752 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 748 = false ∨ valuationOf q 750 = false ∨ valuationOf q 753 = true := by
  have hs : count752 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (748)) (literal (valuationOf q) (750)) (literal (valuationOf q) (753)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count752 q) 1 1 (meaning748 q) (meaning750 q) (meaning753 q) hs
  change valuationOf q 748 = false ∨ valuationOf q 750 = false ∨ valuationOf q 753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 748 = false ∨ valuation q 750 = false ∨ valuation q 753 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 748 = false ∨ valuationOf q 751 = false ∨ valuationOf q 754 = true := by
  have hs : count752 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (748)) (literal (valuationOf q) (751)) (literal (valuationOf q) (754)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count752 q) 1 2 (meaning748 q) (meaning751 q) (meaning754 q) hs
  change valuationOf q 748 = false ∨ valuationOf q 751 = false ∨ valuationOf q 754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 748 = false ∨ valuation q 751 = false ∨ valuation q 754 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 749 = false ∨ valuationOf q 753 = true := by
  have hs : count752 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_left (literal (valuationOf q) (749)) (literal (valuationOf q) (753)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count752 q) 2 (meaning749 q) (meaning753 q) hs
  change valuationOf q 749 = false ∨ valuationOf q 753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 749 = false ∨ valuation q 753 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 749 = false ∨ valuationOf q 750 = false ∨ valuationOf q 754 = true := by
  have hs : count752 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (749)) (literal (valuationOf q) (750)) (literal (valuationOf q) (754)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count752 q) 2 1 (meaning749 q) (meaning750 q) (meaning754 q) hs
  change valuationOf q 749 = false ∨ valuationOf q 750 = false ∨ valuationOf q 754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 749 = false ∨ valuation q 750 = false ∨ valuation q 754 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 749 = false ∨ valuationOf q 751 = false ∨ valuationOf q 755 = true := by
  have hs : count752 q = (countLit q [-6, -9]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -9]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (749)) (literal (valuationOf q) (751)) (literal (valuationOf q) (755)) (countLit q [-6, -9]) (countLit q [-11, -12]) (count752 q) 2 2 (meaning749 q) (meaning751 q) (meaning755 q) hs
  change valuationOf q 749 = false ∨ valuationOf q 751 = false ∨ valuationOf q 755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 749 = false ∨ valuation q 751 = false ∨ valuation q 755 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 753 = false ∨ valuationOf q 757 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_right (literal (valuationOf q) (753)) (literal (valuationOf q) (757)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 2 (meaning753 q) (meaning757 q) hs
  change valuationOf q 753 = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 753 = false ∨ valuation q 757 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 754 = false ∨ valuationOf q 758 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_right (literal (valuationOf q) (754)) (literal (valuationOf q) (758)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 3 (meaning754 q) (meaning758 q) hs
  change valuationOf q 754 = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 754 = false ∨ valuation q 758 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 755 = false ∨ valuationOf q 759 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_right (literal (valuationOf q) (755)) (literal (valuationOf q) (759)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 4 (meaning755 q) (meaning759 q) hs
  change valuationOf q 755 = false ∨ valuationOf q 759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 755 = false ∨ valuation q 759 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 745 = false ∨ valuationOf q 756 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_left (literal (valuationOf q) (745)) (literal (valuationOf q) (756)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 1 (meaning745 q) (meaning756 q) hs
  change valuationOf q 745 = false ∨ valuationOf q 756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 745 = false ∨ valuation q 756 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 745 = false ∨ valuationOf q 752 = false ∨ valuationOf q 757 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (745)) (literal (valuationOf q) (752)) (literal (valuationOf q) (757)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 1 1 (meaning745 q) (meaning752 q) (meaning757 q) hs
  change valuationOf q 745 = false ∨ valuationOf q 752 = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 745 = false ∨ valuation q 752 = false ∨ valuation q 757 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 745 = false ∨ valuationOf q 753 = false ∨ valuationOf q 758 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (745)) (literal (valuationOf q) (753)) (literal (valuationOf q) (758)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 1 2 (meaning745 q) (meaning753 q) (meaning758 q) hs
  change valuationOf q 745 = false ∨ valuationOf q 753 = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 745 = false ∨ valuation q 753 = false ∨ valuation q 758 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 745 = false ∨ valuationOf q 754 = false ∨ valuationOf q 759 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (745)) (literal (valuationOf q) (754)) (literal (valuationOf q) (759)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 1 3 (meaning745 q) (meaning754 q) (meaning759 q) hs
  change valuationOf q 745 = false ∨ valuationOf q 754 = false ∨ valuationOf q 759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 745 = false ∨ valuation q 754 = false ∨ valuation q 759 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 746 = false ∨ valuationOf q 757 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_left (literal (valuationOf q) (746)) (literal (valuationOf q) (757)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 2 (meaning746 q) (meaning757 q) hs
  change valuationOf q 746 = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 746 = false ∨ valuation q 757 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 746 = false ∨ valuationOf q 752 = false ∨ valuationOf q 758 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (746)) (literal (valuationOf q) (752)) (literal (valuationOf q) (758)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 2 1 (meaning746 q) (meaning752 q) (meaning758 q) hs
  change valuationOf q 746 = false ∨ valuationOf q 752 = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 746 = false ∨ valuation q 752 = false ∨ valuation q 758 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 746 = false ∨ valuationOf q 753 = false ∨ valuationOf q 759 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (746)) (literal (valuationOf q) (753)) (literal (valuationOf q) (759)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 2 2 (meaning746 q) (meaning753 q) (meaning759 q) hs
  change valuationOf q 746 = false ∨ valuationOf q 753 = false ∨ valuationOf q 759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 746 = false ∨ valuation q 753 = false ∨ valuation q 759 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 746 = false ∨ valuationOf q 754 = false ∨ valuationOf q 760 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (746)) (literal (valuationOf q) (754)) (literal (valuationOf q) (760)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 2 3 (meaning746 q) (meaning754 q) (meaning760 q) hs
  change valuationOf q 746 = false ∨ valuationOf q 754 = false ∨ valuationOf q 760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 746 = false ∨ valuation q 754 = false ∨ valuation q 760 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 747 = false ∨ valuationOf q 758 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_left (literal (valuationOf q) (747)) (literal (valuationOf q) (758)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 3 (meaning747 q) (meaning758 q) hs
  change valuationOf q 747 = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 747 = false ∨ valuation q 758 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 747 = false ∨ valuationOf q 752 = false ∨ valuationOf q 759 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (747)) (literal (valuationOf q) (752)) (literal (valuationOf q) (759)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 3 1 (meaning747 q) (meaning752 q) (meaning759 q) hs
  change valuationOf q 747 = false ∨ valuationOf q 752 = false ∨ valuationOf q 759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 747 = false ∨ valuation q 752 = false ∨ valuation q 759 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 747 = false ∨ valuationOf q 753 = false ∨ valuationOf q 760 = true := by
  have hs : count756 q = (countLit q [-1, -4, -5]) + (countLit q [-6, -9, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5]) (l₂ := [-6, -9, -11, -12])
  have hm := merge_two (literal (valuationOf q) (747)) (literal (valuationOf q) (753)) (literal (valuationOf q) (760)) (countLit q [-1, -4, -5]) (countLit q [-6, -9, -11, -12]) (count756 q) 3 2 (meaning747 q) (meaning753 q) (meaning760 q) hs
  change valuationOf q 747 = false ∨ valuationOf q 753 = false ∨ valuationOf q 760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 747 = false ∨ valuation q 753 = false ∨ valuation q 760 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 763 = true := by
  have hs : count763 q = (countLit q [-17]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (763)) (countLit q [-17]) (countLit q [-18]) (count763 q) 1 (meaningNeg18 q) (meaning763 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 763 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 763 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 763 = true := by
  have hs : count763 q = (countLit q [-17]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (763)) (countLit q [-17]) (countLit q [-18]) (count763 q) 1 (meaningNeg17 q) (meaning763 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 763 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 763 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 18 = true ∨ valuationOf q 764 = true := by
  have hs : count763 q = (countLit q [-17]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (764)) (countLit q [-17]) (countLit q [-18]) (count763 q) 1 1 (meaningNeg17 q) (meaningNeg18 q) (meaning764 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 764 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 18 = true ∨ valuation q 764 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 763 = false ∨ valuationOf q 765 = true := by
  have hs : count765 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_right (literal (valuationOf q) (763)) (literal (valuationOf q) (765)) (countLit q [-15]) (countLit q [-17, -18]) (count765 q) 1 (meaning763 q) (meaning765 q) hs
  change valuationOf q 763 = false ∨ valuationOf q 765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 763 = false ∨ valuation q 765 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E185.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112185
