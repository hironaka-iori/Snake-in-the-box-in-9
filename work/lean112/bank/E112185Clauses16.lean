import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 779 = false ∨ valuationOf q 789 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (758)) (literal (valuationOf q) (779)) (literal (valuationOf q) (789)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 3 4 (meaning758 q) (meaning779 q) (meaning789 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 779 = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 779 = false ∨ valuation q 789 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 780 = false ∨ valuationOf q 790 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (758)) (literal (valuationOf q) (780)) (literal (valuationOf q) (790)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 3 5 (meaning758 q) (meaning780 q) (meaning790 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 780 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 780 = false ∨ valuation q 790 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 759 = false ∨ valuationOf q 776 = false ∨ valuationOf q 787 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (759)) (literal (valuationOf q) (776)) (literal (valuationOf q) (787)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 4 1 (meaning759 q) (meaning776 q) (meaning787 q) hs
  change valuationOf q 759 = false ∨ valuationOf q 776 = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 759 = false ∨ valuation q 776 = false ∨ valuation q 787 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 759 = false ∨ valuationOf q 777 = false ∨ valuationOf q 788 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (759)) (literal (valuationOf q) (777)) (literal (valuationOf q) (788)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 4 2 (meaning759 q) (meaning777 q) (meaning788 q) hs
  change valuationOf q 759 = false ∨ valuationOf q 777 = false ∨ valuationOf q 788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 759 = false ∨ valuation q 777 = false ∨ valuation q 788 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 759 = false ∨ valuationOf q 778 = false ∨ valuationOf q 789 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (759)) (literal (valuationOf q) (778)) (literal (valuationOf q) (789)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 4 3 (meaning759 q) (meaning778 q) (meaning789 q) hs
  change valuationOf q 759 = false ∨ valuationOf q 778 = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 759 = false ∨ valuation q 778 = false ∨ valuation q 789 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 759 = false ∨ valuationOf q 779 = false ∨ valuationOf q 790 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (759)) (literal (valuationOf q) (779)) (literal (valuationOf q) (790)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 4 4 (meaning759 q) (meaning779 q) (meaning790 q) hs
  change valuationOf q 759 = false ∨ valuationOf q 779 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 759 = false ∨ valuation q 779 = false ∨ valuation q 790 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 760 = false ∨ valuationOf q 776 = false ∨ valuationOf q 788 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (760)) (literal (valuationOf q) (776)) (literal (valuationOf q) (788)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 5 1 (meaning760 q) (meaning776 q) (meaning788 q) hs
  change valuationOf q 760 = false ∨ valuationOf q 776 = false ∨ valuationOf q 788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 760 = false ∨ valuation q 776 = false ∨ valuation q 788 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 760 = false ∨ valuationOf q 777 = false ∨ valuationOf q 789 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (760)) (literal (valuationOf q) (777)) (literal (valuationOf q) (789)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 5 2 (meaning760 q) (meaning777 q) (meaning789 q) hs
  change valuationOf q 760 = false ∨ valuationOf q 777 = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 760 = false ∨ valuation q 777 = false ∨ valuation q 789 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 760 = false ∨ valuationOf q 778 = false ∨ valuationOf q 790 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (760)) (literal (valuationOf q) (778)) (literal (valuationOf q) (790)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 5 3 (meaning760 q) (meaning778 q) (meaning790 q) hs
  change valuationOf q 760 = false ∨ valuationOf q 778 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 760 = false ∨ valuation q 778 = false ∨ valuation q 790 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 797 = true := by
  have hs : count797 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (797)) (countLit q [-29]) (countLit q [-31]) (count797 q) 1 (meaningNeg29 q) (meaning797 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 797 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 31 = true ∨ valuationOf q 798 = true := by
  have hs : count797 q = (countLit q [-29]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-29)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (798)) (countLit q [-29]) (countLit q [-31]) (count797 q) 1 1 (meaningNeg29 q) (meaningNeg31 q) (meaning798 q) hs
  change (! (valuationOf q 29)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 31 = true ∨ valuation q 798 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 797 = false ∨ valuationOf q 799 = true := by
  have hs : count799 q = (countLit q [-27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (797)) (literal (valuationOf q) (799)) (countLit q [-27]) (countLit q [-29, -31]) (count799 q) 1 (meaning797 q) (meaning799 q) hs
  change valuationOf q 797 = false ∨ valuationOf q 799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 797 = false ∨ valuation q 799 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 798 = false ∨ valuationOf q 800 = true := by
  have hs : count799 q = (countLit q [-27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -31])
  have hm := merge_right (literal (valuationOf q) (798)) (literal (valuationOf q) (800)) (countLit q [-27]) (countLit q [-29, -31]) (count799 q) 2 (meaning798 q) (meaning800 q) hs
  change valuationOf q 798 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 798 = false ∨ valuation q 800 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 797 = false ∨ valuationOf q 800 = true := by
  have hs : count799 q = (countLit q [-27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (797)) (literal (valuationOf q) (800)) (countLit q [-27]) (countLit q [-29, -31]) (count799 q) 1 1 (meaningNeg27 q) (meaning797 q) (meaning800 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 797 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 797 = false ∨ valuation q 800 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 798 = false ∨ valuationOf q 801 = true := by
  have hs : count799 q = (countLit q [-27]) + (countLit q [-29, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29, -31])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (798)) (literal (valuationOf q) (801)) (countLit q [-27]) (countLit q [-29, -31]) (count799 q) 1 2 (meaningNeg27 q) (meaning798 q) (meaning801 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 798 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 798 = false ∨ valuation q 801 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 802 = true := by
  have hs : count802 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_right (literal (valuationOf q) (-34)) (literal (valuationOf q) (802)) (countLit q [-32]) (countLit q [-34]) (count802 q) 1 (meaningNeg34 q) (meaning802 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 802 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 802 = true := by
  have hs : count802 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (802)) (countLit q [-32]) (countLit q [-34]) (count802 q) 1 (meaningNeg32 q) (meaning802 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 802 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 34 = true ∨ valuationOf q 803 = true := by
  have hs : count802 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-34)) (literal (valuationOf q) (803)) (countLit q [-32]) (countLit q [-34]) (count802 q) 1 1 (meaningNeg32 q) (meaningNeg34 q) (meaning803 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 34)) = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 803 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 804 = true := by
  have hs : count804 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (804)) (countLit q [-37]) (countLit q [-39]) (count804 q) 1 (meaningNeg39 q) (meaning804 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 804 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 804 = true := by
  have hs : count804 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-37)) (literal (valuationOf q) (804)) (countLit q [-37]) (countLit q [-39]) (count804 q) 1 (meaningNeg37 q) (meaning804 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 804 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 39 = true ∨ valuationOf q 805 = true := by
  have hs : count804 q = (countLit q [-37]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-37]) (l₂ := [-39])
  have hm := merge_two (literal (valuationOf q) (-37)) (literal (valuationOf q) (-39)) (literal (valuationOf q) (805)) (countLit q [-37]) (countLit q [-39]) (count804 q) 1 1 (meaningNeg37 q) (meaningNeg39 q) (meaning805 q) hs
  change (! (valuationOf q 37)) = false ∨ (! (valuationOf q 39)) = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 39 = true ∨ valuation q 805 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 806 = true := by
  have hs : count806 q = (countLit q [-32, -34]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-37, -39])
  have hm := merge_right (literal (valuationOf q) (804)) (literal (valuationOf q) (806)) (countLit q [-32, -34]) (countLit q [-37, -39]) (count806 q) 1 (meaning804 q) (meaning806 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 806 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 807 = true := by
  have hs : count806 q = (countLit q [-32, -34]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-37, -39])
  have hm := merge_right (literal (valuationOf q) (805)) (literal (valuationOf q) (807)) (countLit q [-32, -34]) (countLit q [-37, -39]) (count806 q) 2 (meaning805 q) (meaning807 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 807 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 806 = true := by
  have hs : count806 q = (countLit q [-32, -34]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-37, -39])
  have hm := merge_left (literal (valuationOf q) (802)) (literal (valuationOf q) (806)) (countLit q [-32, -34]) (countLit q [-37, -39]) (count806 q) 1 (meaning802 q) (meaning806 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 806 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 804 = false ∨ valuationOf q 807 = true := by
  have hs : count806 q = (countLit q [-32, -34]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-37, -39])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (804)) (literal (valuationOf q) (807)) (countLit q [-32, -34]) (countLit q [-37, -39]) (count806 q) 1 1 (meaning802 q) (meaning804 q) (meaning807 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 804 = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 804 = false ∨ valuation q 807 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 805 = false ∨ valuationOf q 808 = true := by
  have hs : count806 q = (countLit q [-32, -34]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-37, -39])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (805)) (literal (valuationOf q) (808)) (countLit q [-32, -34]) (countLit q [-37, -39]) (count806 q) 1 2 (meaning802 q) (meaning805 q) (meaning808 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 805 = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 805 = false ∨ valuation q 808 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 807 = true := by
  have hs : count806 q = (countLit q [-32, -34]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-37, -39])
  have hm := merge_left (literal (valuationOf q) (803)) (literal (valuationOf q) (807)) (countLit q [-32, -34]) (countLit q [-37, -39]) (count806 q) 2 (meaning803 q) (meaning807 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 807 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 804 = false ∨ valuationOf q 808 = true := by
  have hs : count806 q = (countLit q [-32, -34]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-37, -39])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (804)) (literal (valuationOf q) (808)) (countLit q [-32, -34]) (countLit q [-37, -39]) (count806 q) 2 1 (meaning803 q) (meaning804 q) (meaning808 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 804 = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 804 = false ∨ valuation q 808 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 805 = false ∨ valuationOf q 809 = true := by
  have hs : count806 q = (countLit q [-32, -34]) + (countLit q [-37, -39]) := List.countP_append (p := literal q) (l₁ := [-32, -34]) (l₂ := [-37, -39])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (805)) (literal (valuationOf q) (809)) (countLit q [-32, -34]) (countLit q [-37, -39]) (count806 q) 2 2 (meaning803 q) (meaning805 q) (meaning809 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 805 = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 805 = false ∨ valuation q 809 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 810 = true := by
  have hs : count810 q = (countLit q [-27, -29, -31]) + (countLit q [-32, -34, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-32, -34, -37, -39])
  have hm := merge_left (literal (valuationOf q) (799)) (literal (valuationOf q) (810)) (countLit q [-27, -29, -31]) (countLit q [-32, -34, -37, -39]) (count810 q) 1 (meaning799 q) (meaning810 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 810 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 806 = false ∨ valuationOf q 811 = true := by
  have hs : count810 q = (countLit q [-27, -29, -31]) + (countLit q [-32, -34, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-32, -34, -37, -39])
  have hm := merge_two (literal (valuationOf q) (799)) (literal (valuationOf q) (806)) (literal (valuationOf q) (811)) (countLit q [-27, -29, -31]) (countLit q [-32, -34, -37, -39]) (count810 q) 1 1 (meaning799 q) (meaning806 q) (meaning811 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 806 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 806 = false ∨ valuation q 811 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 807 = false ∨ valuationOf q 812 = true := by
  have hs : count810 q = (countLit q [-27, -29, -31]) + (countLit q [-32, -34, -37, -39]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31]) (l₂ := [-32, -34, -37, -39])
  have hm := merge_two (literal (valuationOf q) (799)) (literal (valuationOf q) (807)) (literal (valuationOf q) (812)) (countLit q [-27, -29, -31]) (countLit q [-32, -34, -37, -39]) (count810 q) 1 2 (meaning799 q) (meaning807 q) (meaning812 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 807 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 807 = false ∨ valuation q 812 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E185.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112185
