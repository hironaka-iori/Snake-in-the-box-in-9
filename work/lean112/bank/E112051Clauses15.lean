import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 787 = false ∨ valuationOf q 788 = false ∨ valuationOf q 792 = true := by
  have hs : count790 q = (countLit q [-8, -9]) + (countLit q [-10, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-10, -15])
  have hm := merge_two (literal (valuationOf q) (787)) (literal (valuationOf q) (788)) (literal (valuationOf q) (792)) (countLit q [-8, -9]) (countLit q [-10, -15]) (count790 q) 2 1 (meaning787 q) (meaning788 q) (meaning792 q) hs
  change valuationOf q 787 = false ∨ valuationOf q 788 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 787 = false ∨ valuation q 788 = false ∨ valuation q 792 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 787 = false ∨ valuationOf q 789 = false ∨ valuationOf q 793 = true := by
  have hs : count790 q = (countLit q [-8, -9]) + (countLit q [-10, -15]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-10, -15])
  have hm := merge_two (literal (valuationOf q) (787)) (literal (valuationOf q) (789)) (literal (valuationOf q) (793)) (countLit q [-8, -9]) (countLit q [-10, -15]) (count790 q) 2 2 (meaning787 q) (meaning789 q) (meaning793 q) hs
  change valuationOf q 787 = false ∨ valuationOf q 789 = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 787 = false ∨ valuation q 789 = false ∨ valuation q 793 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 794 = true := by
  have hs : count794 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -9, -10, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -9, -10, -15])
  have hm := merge_right (literal (valuationOf q) (790)) (literal (valuationOf q) (794)) (countLit q [-1, -3, -6]) (countLit q [-8, -9, -10, -15]) (count794 q) 1 (meaning790 q) (meaning794 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 794 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 794 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 791 = false ∨ valuationOf q 795 = true := by
  have hs : count794 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -9, -10, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -9, -10, -15])
  have hm := merge_right (literal (valuationOf q) (791)) (literal (valuationOf q) (795)) (countLit q [-1, -3, -6]) (countLit q [-8, -9, -10, -15]) (count794 q) 2 (meaning791 q) (meaning795 q) hs
  change valuationOf q 791 = false ∨ valuationOf q 795 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 791 = false ∨ valuation q 795 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 792 = false ∨ valuationOf q 796 = true := by
  have hs : count794 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -9, -10, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -9, -10, -15])
  have hm := merge_right (literal (valuationOf q) (792)) (literal (valuationOf q) (796)) (countLit q [-1, -3, -6]) (countLit q [-8, -9, -10, -15]) (count794 q) 3 (meaning792 q) (meaning796 q) hs
  change valuationOf q 792 = false ∨ valuationOf q 796 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 792 = false ∨ valuation q 796 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 793 = false ∨ valuationOf q 797 = true := by
  have hs : count794 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -9, -10, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -9, -10, -15])
  have hm := merge_right (literal (valuationOf q) (793)) (literal (valuationOf q) (797)) (countLit q [-1, -3, -6]) (countLit q [-8, -9, -10, -15]) (count794 q) 4 (meaning793 q) (meaning797 q) hs
  change valuationOf q 793 = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 793 = false ∨ valuation q 797 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 783 = false ∨ valuationOf q 794 = true := by
  have hs : count794 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -9, -10, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -9, -10, -15])
  have hm := merge_left (literal (valuationOf q) (783)) (literal (valuationOf q) (794)) (countLit q [-1, -3, -6]) (countLit q [-8, -9, -10, -15]) (count794 q) 1 (meaning783 q) (meaning794 q) hs
  change valuationOf q 783 = false ∨ valuationOf q 794 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 783 = false ∨ valuation q 794 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 783 = false ∨ valuationOf q 790 = false ∨ valuationOf q 795 = true := by
  have hs : count794 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -9, -10, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -9, -10, -15])
  have hm := merge_two (literal (valuationOf q) (783)) (literal (valuationOf q) (790)) (literal (valuationOf q) (795)) (countLit q [-1, -3, -6]) (countLit q [-8, -9, -10, -15]) (count794 q) 1 1 (meaning783 q) (meaning790 q) (meaning795 q) hs
  change valuationOf q 783 = false ∨ valuationOf q 790 = false ∨ valuationOf q 795 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 783 = false ∨ valuation q 790 = false ∨ valuation q 795 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 783 = false ∨ valuationOf q 791 = false ∨ valuationOf q 796 = true := by
  have hs : count794 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -9, -10, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -9, -10, -15])
  have hm := merge_two (literal (valuationOf q) (783)) (literal (valuationOf q) (791)) (literal (valuationOf q) (796)) (countLit q [-1, -3, -6]) (countLit q [-8, -9, -10, -15]) (count794 q) 1 2 (meaning783 q) (meaning791 q) (meaning796 q) hs
  change valuationOf q 783 = false ∨ valuationOf q 791 = false ∨ valuationOf q 796 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 783 = false ∨ valuation q 791 = false ∨ valuation q 796 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 783 = false ∨ valuationOf q 792 = false ∨ valuationOf q 797 = true := by
  have hs : count794 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -9, -10, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -9, -10, -15])
  have hm := merge_two (literal (valuationOf q) (783)) (literal (valuationOf q) (792)) (literal (valuationOf q) (797)) (countLit q [-1, -3, -6]) (countLit q [-8, -9, -10, -15]) (count794 q) 1 3 (meaning783 q) (meaning792 q) (meaning797 q) hs
  change valuationOf q 783 = false ∨ valuationOf q 792 = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 783 = false ∨ valuation q 792 = false ∨ valuation q 797 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 784 = false ∨ valuationOf q 795 = true := by
  have hs : count794 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -9, -10, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -9, -10, -15])
  have hm := merge_left (literal (valuationOf q) (784)) (literal (valuationOf q) (795)) (countLit q [-1, -3, -6]) (countLit q [-8, -9, -10, -15]) (count794 q) 2 (meaning784 q) (meaning795 q) hs
  change valuationOf q 784 = false ∨ valuationOf q 795 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 784 = false ∨ valuation q 795 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 784 = false ∨ valuationOf q 790 = false ∨ valuationOf q 796 = true := by
  have hs : count794 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -9, -10, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -9, -10, -15])
  have hm := merge_two (literal (valuationOf q) (784)) (literal (valuationOf q) (790)) (literal (valuationOf q) (796)) (countLit q [-1, -3, -6]) (countLit q [-8, -9, -10, -15]) (count794 q) 2 1 (meaning784 q) (meaning790 q) (meaning796 q) hs
  change valuationOf q 784 = false ∨ valuationOf q 790 = false ∨ valuationOf q 796 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 784 = false ∨ valuation q 790 = false ∨ valuation q 796 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 784 = false ∨ valuationOf q 791 = false ∨ valuationOf q 797 = true := by
  have hs : count794 q = (countLit q [-1, -3, -6]) + (countLit q [-8, -9, -10, -15]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6]) (l₂ := [-8, -9, -10, -15])
  have hm := merge_two (literal (valuationOf q) (784)) (literal (valuationOf q) (791)) (literal (valuationOf q) (797)) (countLit q [-1, -3, -6]) (countLit q [-8, -9, -10, -15]) (count794 q) 2 2 (meaning784 q) (meaning791 q) (meaning797 q) hs
  change valuationOf q 784 = false ∨ valuationOf q 791 = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 784 = false ∨ valuation q 791 = false ∨ valuation q 797 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 801 = true := by
  have hs : count801 q = (countLit q [-17]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-20])
  have hm := merge_right (literal (valuationOf q) (-20)) (literal (valuationOf q) (801)) (countLit q [-17]) (countLit q [-20]) (count801 q) 1 (meaningNeg20 q) (meaning801 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 801 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 801 = true := by
  have hs : count801 q = (countLit q [-17]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-20])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (801)) (countLit q [-17]) (countLit q [-20]) (count801 q) 1 (meaningNeg17 q) (meaning801 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 801 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 20 = true ∨ valuationOf q 802 = true := by
  have hs : count801 q = (countLit q [-17]) + (countLit q [-20]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-20])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-20)) (literal (valuationOf q) (802)) (countLit q [-17]) (countLit q [-20]) (count801 q) 1 1 (meaningNeg17 q) (meaningNeg20 q) (meaning802 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 20)) = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 20 = true ∨ valuation q 802 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 803 = true := by
  have hs : count803 q = (countLit q [-16]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -20])
  have hm := merge_right (literal (valuationOf q) (801)) (literal (valuationOf q) (803)) (countLit q [-16]) (countLit q [-17, -20]) (count803 q) 1 (meaning801 q) (meaning803 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 803 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 804 = true := by
  have hs : count803 q = (countLit q [-16]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -20])
  have hm := merge_right (literal (valuationOf q) (802)) (literal (valuationOf q) (804)) (countLit q [-16]) (countLit q [-17, -20]) (count803 q) 2 (meaning802 q) (meaning804 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 804 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 803 = true := by
  have hs : count803 q = (countLit q [-16]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -20])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (803)) (countLit q [-16]) (countLit q [-17, -20]) (count803 q) 1 (meaningNeg16 q) (meaning803 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 803 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 801 = false ∨ valuationOf q 804 = true := by
  have hs : count803 q = (countLit q [-16]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -20])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (801)) (literal (valuationOf q) (804)) (countLit q [-16]) (countLit q [-17, -20]) (count803 q) 1 1 (meaningNeg16 q) (meaning801 q) (meaning804 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 801 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 801 = false ∨ valuation q 804 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 802 = false ∨ valuationOf q 805 = true := by
  have hs : count803 q = (countLit q [-16]) + (countLit q [-17, -20]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -20])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (802)) (literal (valuationOf q) (805)) (countLit q [-16]) (countLit q [-17, -20]) (count803 q) 1 2 (meaningNeg16 q) (meaning802 q) (meaning805 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 802 = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 802 = false ∨ valuation q 805 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 806 = true := by
  have hs : count806 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (806)) (countLit q [-24]) (countLit q [-26]) (count806 q) 1 (meaningNeg26 q) (meaning806 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 806 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 806 = true := by
  have hs : count806 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (806)) (countLit q [-24]) (countLit q [-26]) (count806 q) 1 (meaningNeg24 q) (meaning806 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 806 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 26 = true ∨ valuationOf q 807 = true := by
  have hs : count806 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (807)) (countLit q [-24]) (countLit q [-26]) (count806 q) 1 1 (meaningNeg24 q) (meaningNeg26 q) (meaning807 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 26 = true ∨ valuation q 807 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 808 = true := by
  have hs : count808 q = (countLit q [-27]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (808)) (countLit q [-27]) (countLit q [-30]) (count808 q) 1 (meaningNeg30 q) (meaning808 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 808 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 808 = true := by
  have hs : count808 q = (countLit q [-27]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (808)) (countLit q [-27]) (countLit q [-30]) (count808 q) 1 (meaningNeg27 q) (meaning808 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 808 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 30 = true ∨ valuationOf q 809 = true := by
  have hs : count808 q = (countLit q [-27]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (809)) (countLit q [-27]) (countLit q [-30]) (count808 q) 1 1 (meaningNeg27 q) (meaningNeg30 q) (meaning809 q) hs
  change (! (valuationOf q 27)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 30 = true ∨ valuation q 809 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 808 = false ∨ valuationOf q 810 = true := by
  have hs : count810 q = (countLit q [-24, -26]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-27, -30])
  have hm := merge_right (literal (valuationOf q) (808)) (literal (valuationOf q) (810)) (countLit q [-24, -26]) (countLit q [-27, -30]) (count810 q) 1 (meaning808 q) (meaning810 q) hs
  change valuationOf q 808 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 808 = false ∨ valuation q 810 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 811 = true := by
  have hs : count810 q = (countLit q [-24, -26]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-27, -30])
  have hm := merge_right (literal (valuationOf q) (809)) (literal (valuationOf q) (811)) (countLit q [-24, -26]) (countLit q [-27, -30]) (count810 q) 2 (meaning809 q) (meaning811 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 811 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 806 = false ∨ valuationOf q 810 = true := by
  have hs : count810 q = (countLit q [-24, -26]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-27, -30])
  have hm := merge_left (literal (valuationOf q) (806)) (literal (valuationOf q) (810)) (countLit q [-24, -26]) (countLit q [-27, -30]) (count810 q) 1 (meaning806 q) (meaning810 q) hs
  change valuationOf q 806 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 806 = false ∨ valuation q 810 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 806 = false ∨ valuationOf q 808 = false ∨ valuationOf q 811 = true := by
  have hs : count810 q = (countLit q [-24, -26]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-27, -30])
  have hm := merge_two (literal (valuationOf q) (806)) (literal (valuationOf q) (808)) (literal (valuationOf q) (811)) (countLit q [-24, -26]) (countLit q [-27, -30]) (count810 q) 1 1 (meaning806 q) (meaning808 q) (meaning811 q) hs
  change valuationOf q 806 = false ∨ valuationOf q 808 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 806 = false ∨ valuation q 808 = false ∨ valuation q 811 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 806 = false ∨ valuationOf q 809 = false ∨ valuationOf q 812 = true := by
  have hs : count810 q = (countLit q [-24, -26]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-27, -30])
  have hm := merge_two (literal (valuationOf q) (806)) (literal (valuationOf q) (809)) (literal (valuationOf q) (812)) (countLit q [-24, -26]) (countLit q [-27, -30]) (count810 q) 1 2 (meaning806 q) (meaning809 q) (meaning812 q) hs
  change valuationOf q 806 = false ∨ valuationOf q 809 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 806 = false ∨ valuation q 809 = false ∨ valuation q 812 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E051.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112051
