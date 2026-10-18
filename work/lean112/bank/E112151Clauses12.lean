import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 801 = true := by
  have hs : count801 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (801)) (countLit q [-46]) (countLit q [-49]) (count801 q) 1 (meaningNeg46 q) (meaning801 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 801 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 49 = true ∨ valuationOf q 802 = true := by
  have hs : count801 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (802)) (countLit q [-46]) (countLit q [-49]) (count801 q) 1 1 (meaningNeg46 q) (meaningNeg49 q) (meaning802 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 49 = true ∨ valuation q 802 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 803 = true := by
  have hs : count803 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (803)) (countLit q [-53]) (countLit q [-55]) (count803 q) 1 (meaningNeg55 q) (meaning803 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 803 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 803 = true := by
  have hs : count803 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (803)) (countLit q [-53]) (countLit q [-55]) (count803 q) 1 (meaningNeg53 q) (meaning803 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 803 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 55 = true ∨ valuationOf q 804 = true := by
  have hs : count803 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (804)) (countLit q [-53]) (countLit q [-55]) (count803 q) 1 1 (meaningNeg53 q) (meaningNeg55 q) (meaning804 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 804 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 805 = true := by
  have hs : count805 q = (countLit q [-46, -49]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-46, -49]) (l₂ := [-53, -55])
  have hm := merge_right (literal (valuationOf q) (803)) (literal (valuationOf q) (805)) (countLit q [-46, -49]) (countLit q [-53, -55]) (count805 q) 1 (meaning803 q) (meaning805 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 805 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 806 = true := by
  have hs : count805 q = (countLit q [-46, -49]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-46, -49]) (l₂ := [-53, -55])
  have hm := merge_right (literal (valuationOf q) (804)) (literal (valuationOf q) (806)) (countLit q [-46, -49]) (countLit q [-53, -55]) (count805 q) 2 (meaning804 q) (meaning806 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 806 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 805 = true := by
  have hs : count805 q = (countLit q [-46, -49]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-46, -49]) (l₂ := [-53, -55])
  have hm := merge_left (literal (valuationOf q) (801)) (literal (valuationOf q) (805)) (countLit q [-46, -49]) (countLit q [-53, -55]) (count805 q) 1 (meaning801 q) (meaning805 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 805 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 803 = false ∨ valuationOf q 806 = true := by
  have hs : count805 q = (countLit q [-46, -49]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-46, -49]) (l₂ := [-53, -55])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (803)) (literal (valuationOf q) (806)) (countLit q [-46, -49]) (countLit q [-53, -55]) (count805 q) 1 1 (meaning801 q) (meaning803 q) (meaning806 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 803 = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 803 = false ∨ valuation q 806 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 806 = true := by
  have hs : count805 q = (countLit q [-46, -49]) + (countLit q [-53, -55]) := List.countP_append (p := literal q) (l₁ := [-46, -49]) (l₂ := [-53, -55])
  have hm := merge_left (literal (valuationOf q) (802)) (literal (valuationOf q) (806)) (countLit q [-46, -49]) (countLit q [-53, -55]) (count805 q) 2 (meaning802 q) (meaning806 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 806 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 809 = true := by
  have hs : count809 q = (countLit q [-41, -42, -45]) + (countLit q [-46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -45]) (l₂ := [-46, -49, -53, -55])
  have hm := merge_right (literal (valuationOf q) (805)) (literal (valuationOf q) (809)) (countLit q [-41, -42, -45]) (countLit q [-46, -49, -53, -55]) (count809 q) 1 (meaning805 q) (meaning809 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 809 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 806 = false ∨ valuationOf q 810 = true := by
  have hs : count809 q = (countLit q [-41, -42, -45]) + (countLit q [-46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -45]) (l₂ := [-46, -49, -53, -55])
  have hm := merge_right (literal (valuationOf q) (806)) (literal (valuationOf q) (810)) (countLit q [-41, -42, -45]) (countLit q [-46, -49, -53, -55]) (count809 q) 2 (meaning806 q) (meaning810 q) hs
  change valuationOf q 806 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 806 = false ∨ valuation q 810 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 798 = false ∨ valuationOf q 809 = true := by
  have hs : count809 q = (countLit q [-41, -42, -45]) + (countLit q [-46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -45]) (l₂ := [-46, -49, -53, -55])
  have hm := merge_left (literal (valuationOf q) (798)) (literal (valuationOf q) (809)) (countLit q [-41, -42, -45]) (countLit q [-46, -49, -53, -55]) (count809 q) 1 (meaning798 q) (meaning809 q) hs
  change valuationOf q 798 = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 798 = false ∨ valuation q 809 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 798 = false ∨ valuationOf q 805 = false ∨ valuationOf q 810 = true := by
  have hs : count809 q = (countLit q [-41, -42, -45]) + (countLit q [-46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -45]) (l₂ := [-46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (798)) (literal (valuationOf q) (805)) (literal (valuationOf q) (810)) (countLit q [-41, -42, -45]) (countLit q [-46, -49, -53, -55]) (count809 q) 1 1 (meaning798 q) (meaning805 q) (meaning810 q) hs
  change valuationOf q 798 = false ∨ valuationOf q 805 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 798 = false ∨ valuation q 805 = false ∨ valuation q 810 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 810 = true := by
  have hs : count809 q = (countLit q [-41, -42, -45]) + (countLit q [-46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-41, -42, -45]) (l₂ := [-46, -49, -53, -55])
  have hm := merge_left (literal (valuationOf q) (799)) (literal (valuationOf q) (810)) (countLit q [-41, -42, -45]) (countLit q [-46, -49, -53, -55]) (count809 q) 2 (meaning799 q) (meaning810 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 810 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 816 = true := by
  have hs : count816 q = (countLit q [-28, -29, -30, -33, -36, -38, -40]) + (countLit q [-41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -36, -38, -40]) (l₂ := [-41, -42, -45, -46, -49, -53, -55])
  have hm := merge_left (literal (valuationOf q) (789)) (literal (valuationOf q) (816)) (countLit q [-28, -29, -30, -33, -36, -38, -40]) (countLit q [-41, -42, -45, -46, -49, -53, -55]) (count816 q) 1 (meaning789 q) (meaning816 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 816 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 809 = false ∨ valuationOf q 817 = true := by
  have hs : count816 q = (countLit q [-28, -29, -30, -33, -36, -38, -40]) + (countLit q [-41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -36, -38, -40]) (l₂ := [-41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (809)) (literal (valuationOf q) (817)) (countLit q [-28, -29, -30, -33, -36, -38, -40]) (countLit q [-41, -42, -45, -46, -49, -53, -55]) (count816 q) 1 1 (meaning789 q) (meaning809 q) (meaning817 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 809 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 809 = false ∨ valuation q 817 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 810 = false ∨ valuationOf q 818 = true := by
  have hs : count816 q = (countLit q [-28, -29, -30, -33, -36, -38, -40]) + (countLit q [-41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -36, -38, -40]) (l₂ := [-41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (810)) (literal (valuationOf q) (818)) (countLit q [-28, -29, -30, -33, -36, -38, -40]) (countLit q [-41, -42, -45, -46, -49, -53, -55]) (count816 q) 1 2 (meaning789 q) (meaning810 q) (meaning818 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 810 = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 810 = false ∨ valuation q 818 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 809 = false ∨ valuationOf q 818 = true := by
  have hs : count816 q = (countLit q [-28, -29, -30, -33, -36, -38, -40]) + (countLit q [-41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -36, -38, -40]) (l₂ := [-41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (809)) (literal (valuationOf q) (818)) (countLit q [-28, -29, -30, -33, -36, -38, -40]) (countLit q [-41, -42, -45, -46, -49, -53, -55]) (count816 q) 2 1 (meaning790 q) (meaning809 q) (meaning818 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 809 = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 809 = false ∨ valuation q 818 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 810 = false ∨ valuationOf q 819 = true := by
  have hs : count816 q = (countLit q [-28, -29, -30, -33, -36, -38, -40]) + (countLit q [-41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -36, -38, -40]) (l₂ := [-41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (810)) (literal (valuationOf q) (819)) (countLit q [-28, -29, -30, -33, -36, -38, -40]) (countLit q [-41, -42, -45, -46, -49, -53, -55]) (count816 q) 2 2 (meaning790 q) (meaning810 q) (meaning819 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 810 = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 810 = false ∨ valuation q 819 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 791 = false ∨ valuationOf q 809 = false ∨ valuationOf q 819 = true := by
  have hs : count816 q = (countLit q [-28, -29, -30, -33, -36, -38, -40]) + (countLit q [-41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -36, -38, -40]) (l₂ := [-41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (791)) (literal (valuationOf q) (809)) (literal (valuationOf q) (819)) (countLit q [-28, -29, -30, -33, -36, -38, -40]) (countLit q [-41, -42, -45, -46, -49, -53, -55]) (count816 q) 3 1 (meaning791 q) (meaning809 q) (meaning819 q) hs
  change valuationOf q 791 = false ∨ valuationOf q 809 = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 791 = false ∨ valuation q 809 = false ∨ valuation q 819 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 764 = false ∨ valuationOf q 817 = false ∨ valuationOf q 833 = true := by
  have hs : count830 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (764)) (literal (valuationOf q) (817)) (literal (valuationOf q) (833)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (count830 q) 2 2 (meaning764 q) (meaning817 q) (meaning833 q) hs
  change valuationOf q 764 = false ∨ valuationOf q 817 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 764 = false ∨ valuation q 817 = false ∨ valuation q 833 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 764 = false ∨ valuationOf q 818 = false ∨ valuationOf q 834 = true := by
  have hs : count830 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (764)) (literal (valuationOf q) (818)) (literal (valuationOf q) (834)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (count830 q) 2 3 (meaning764 q) (meaning818 q) (meaning834 q) hs
  change valuationOf q 764 = false ∨ valuationOf q 818 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 764 = false ∨ valuation q 818 = false ∨ valuation q 834 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 764 = false ∨ valuationOf q 819 = false ∨ valuationOf q 835 = true := by
  have hs : count830 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (764)) (literal (valuationOf q) (819)) (literal (valuationOf q) (835)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (count830 q) 2 4 (meaning764 q) (meaning819 q) (meaning835 q) hs
  change valuationOf q 764 = false ∨ valuationOf q 819 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 764 = false ∨ valuation q 819 = false ∨ valuation q 835 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 765 = false ∨ valuationOf q 816 = false ∨ valuationOf q 833 = true := by
  have hs : count830 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (765)) (literal (valuationOf q) (816)) (literal (valuationOf q) (833)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (count830 q) 3 1 (meaning765 q) (meaning816 q) (meaning833 q) hs
  change valuationOf q 765 = false ∨ valuationOf q 816 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 765 = false ∨ valuation q 816 = false ∨ valuation q 833 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 765 = false ∨ valuationOf q 817 = false ∨ valuationOf q 834 = true := by
  have hs : count830 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (765)) (literal (valuationOf q) (817)) (literal (valuationOf q) (834)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (count830 q) 3 2 (meaning765 q) (meaning817 q) (meaning834 q) hs
  change valuationOf q 765 = false ∨ valuationOf q 817 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 765 = false ∨ valuation q 817 = false ∨ valuation q 834 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 765 = false ∨ valuationOf q 818 = false ∨ valuationOf q 835 = true := by
  have hs : count830 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (765)) (literal (valuationOf q) (818)) (literal (valuationOf q) (835)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (count830 q) 3 3 (meaning765 q) (meaning818 q) (meaning835 q) hs
  change valuationOf q 765 = false ∨ valuationOf q 818 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 765 = false ∨ valuation q 818 = false ∨ valuation q 835 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 765 = false ∨ valuationOf q 819 = false ∨ valuationOf q 836 = true := by
  have hs : count830 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (765)) (literal (valuationOf q) (819)) (literal (valuationOf q) (836)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (count830 q) 3 4 (meaning765 q) (meaning819 q) (meaning836 q) hs
  change valuationOf q 765 = false ∨ valuationOf q 819 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 765 = false ∨ valuation q 819 = false ∨ valuation q 836 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 766 = false ∨ valuationOf q 816 = false ∨ valuationOf q 834 = true := by
  have hs : count830 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (766)) (literal (valuationOf q) (816)) (literal (valuationOf q) (834)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (count830 q) 4 1 (meaning766 q) (meaning816 q) (meaning834 q) hs
  change valuationOf q 766 = false ∨ valuationOf q 816 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 766 = false ∨ valuation q 816 = false ∨ valuation q 834 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 766 = false ∨ valuationOf q 817 = false ∨ valuationOf q 835 = true := by
  have hs : count830 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (766)) (literal (valuationOf q) (817)) (literal (valuationOf q) (835)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (count830 q) 4 2 (meaning766 q) (meaning817 q) (meaning835 q) hs
  change valuationOf q 766 = false ∨ valuationOf q 817 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 766 = false ∨ valuation q 817 = false ∨ valuation q 835 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 766 = false ∨ valuationOf q 818 = false ∨ valuationOf q 836 = true := by
  have hs : count830 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (766)) (literal (valuationOf q) (818)) (literal (valuationOf q) (836)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (count830 q) 4 3 (meaning766 q) (meaning818 q) (meaning836 q) hs
  change valuationOf q 766 = false ∨ valuationOf q 818 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 766 = false ∨ valuation q 818 = false ∨ valuation q 836 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 767 = false ∨ valuationOf q 818 = false ∨ valuationOf q 837 = true := by
  have hs : count830 q = (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) + (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (l₂ := [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55])
  have hm := merge_two (literal (valuationOf q) (767)) (literal (valuationOf q) (818)) (literal (valuationOf q) (837)) (countLit q [-1, -3, -5, -7, -9, -10, -13, -14, -17, -20, -22, -24, -25]) (countLit q [-28, -29, -30, -33, -36, -38, -40, -41, -42, -45, -46, -49, -53, -55]) (count830 q) 5 3 (meaning767 q) (meaning818 q) (meaning837 q) hs
  change valuationOf q 767 = false ∨ valuationOf q 818 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 767 = false ∨ valuation q 818 = false ∨ valuation q 837 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E151.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112151
