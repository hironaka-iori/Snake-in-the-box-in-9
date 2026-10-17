import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 787 = true := by
  have hs : count787 q = (countLit q [-2]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4])
  have hm := merge_right (literal (valuationOf q) (-4)) (literal (valuationOf q) (787)) (countLit q [-2]) (countLit q [-4]) (count787 q) 1 (meaningNeg4 q) (meaning787 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 787 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 787 = true := by
  have hs : count787 q = (countLit q [-2]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (787)) (countLit q [-2]) (countLit q [-4]) (count787 q) 1 (meaningNeg2 q) (meaning787 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 787 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 4 = true ∨ valuationOf q 788 = true := by
  have hs : count787 q = (countLit q [-2]) + (countLit q [-4]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-4])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (-4)) (literal (valuationOf q) (788)) (countLit q [-2]) (countLit q [-4]) (count787 q) 1 1 (meaningNeg2 q) (meaningNeg4 q) (meaning788 q) hs
  change (! (valuationOf q 2)) = false ∨ (! (valuationOf q 4)) = false ∨ valuationOf q 788 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 4 = true ∨ valuation q 788 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 787 = false ∨ valuationOf q 789 = true := by
  have hs : count789 q = (countLit q [-1]) + (countLit q [-2, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -4])
  have hm := merge_right (literal (valuationOf q) (787)) (literal (valuationOf q) (789)) (countLit q [-1]) (countLit q [-2, -4]) (count789 q) 1 (meaning787 q) (meaning789 q) hs
  change valuationOf q 787 = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 787 = false ∨ valuation q 789 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 788 = false ∨ valuationOf q 790 = true := by
  have hs : count789 q = (countLit q [-1]) + (countLit q [-2, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -4])
  have hm := merge_right (literal (valuationOf q) (788)) (literal (valuationOf q) (790)) (countLit q [-1]) (countLit q [-2, -4]) (count789 q) 2 (meaning788 q) (meaning790 q) hs
  change valuationOf q 788 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 788 = false ∨ valuation q 790 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 789 = true := by
  have hs : count789 q = (countLit q [-1]) + (countLit q [-2, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -4])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (789)) (countLit q [-1]) (countLit q [-2, -4]) (count789 q) 1 (meaningNeg1 q) (meaning789 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 789 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 787 = false ∨ valuationOf q 790 = true := by
  have hs : count789 q = (countLit q [-1]) + (countLit q [-2, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -4])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (787)) (literal (valuationOf q) (790)) (countLit q [-1]) (countLit q [-2, -4]) (count789 q) 1 1 (meaningNeg1 q) (meaning787 q) (meaning790 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 787 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 787 = false ∨ valuation q 790 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 788 = false ∨ valuationOf q 791 = true := by
  have hs : count789 q = (countLit q [-1]) + (countLit q [-2, -4]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-2, -4])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (788)) (literal (valuationOf q) (791)) (countLit q [-1]) (countLit q [-2, -4]) (count789 q) 1 2 (meaningNeg1 q) (meaning788 q) (meaning791 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 788 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 788 = false ∨ valuation q 791 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 792 = true := by
  have hs : count792 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_right (literal (valuationOf q) (-7)) (literal (valuationOf q) (792)) (countLit q [-6]) (countLit q [-7]) (count792 q) 1 (meaningNeg7 q) (meaning792 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 792 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 792 = true := by
  have hs : count792 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_left (literal (valuationOf q) (-6)) (literal (valuationOf q) (792)) (countLit q [-6]) (countLit q [-7]) (count792 q) 1 (meaningNeg6 q) (meaning792 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 792 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 7 = true ∨ valuationOf q 793 = true := by
  have hs : count792 q = (countLit q [-6]) + (countLit q [-7]) := List.countP_append (p := literal q) (l₁ := [-6]) (l₂ := [-7])
  have hm := merge_two (literal (valuationOf q) (-6)) (literal (valuationOf q) (-7)) (literal (valuationOf q) (793)) (countLit q [-6]) (countLit q [-7]) (count792 q) 1 1 (meaningNeg6 q) (meaningNeg7 q) (meaning793 q) hs
  change (! (valuationOf q 6)) = false ∨ (! (valuationOf q 7)) = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 7 = true ∨ valuation q 793 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 794 = true := by
  have hs : count794 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_right (literal (valuationOf q) (-12)) (literal (valuationOf q) (794)) (countLit q [-11]) (countLit q [-12]) (count794 q) 1 (meaningNeg12 q) (meaning794 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 794 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 794 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 794 = true := by
  have hs : count794 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (794)) (countLit q [-11]) (countLit q [-12]) (count794 q) 1 (meaningNeg11 q) (meaning794 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 794 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 794 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 12 = true ∨ valuationOf q 795 = true := by
  have hs : count794 q = (countLit q [-11]) + (countLit q [-12]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-12])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-12)) (literal (valuationOf q) (795)) (countLit q [-11]) (countLit q [-12]) (count794 q) 1 1 (meaningNeg11 q) (meaningNeg12 q) (meaning795 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 12)) = false ∨ valuationOf q 795 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 12 = true ∨ valuation q 795 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 794 = false ∨ valuationOf q 796 = true := by
  have hs : count796 q = (countLit q [-6, -7]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (794)) (literal (valuationOf q) (796)) (countLit q [-6, -7]) (countLit q [-11, -12]) (count796 q) 1 (meaning794 q) (meaning796 q) hs
  change valuationOf q 794 = false ∨ valuationOf q 796 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 794 = false ∨ valuation q 796 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 795 = false ∨ valuationOf q 797 = true := by
  have hs : count796 q = (countLit q [-6, -7]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-11, -12])
  have hm := merge_right (literal (valuationOf q) (795)) (literal (valuationOf q) (797)) (countLit q [-6, -7]) (countLit q [-11, -12]) (count796 q) 2 (meaning795 q) (meaning797 q) hs
  change valuationOf q 795 = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 795 = false ∨ valuation q 797 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 792 = false ∨ valuationOf q 796 = true := by
  have hs : count796 q = (countLit q [-6, -7]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-11, -12])
  have hm := merge_left (literal (valuationOf q) (792)) (literal (valuationOf q) (796)) (countLit q [-6, -7]) (countLit q [-11, -12]) (count796 q) 1 (meaning792 q) (meaning796 q) hs
  change valuationOf q 792 = false ∨ valuationOf q 796 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 792 = false ∨ valuation q 796 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 792 = false ∨ valuationOf q 794 = false ∨ valuationOf q 797 = true := by
  have hs : count796 q = (countLit q [-6, -7]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (792)) (literal (valuationOf q) (794)) (literal (valuationOf q) (797)) (countLit q [-6, -7]) (countLit q [-11, -12]) (count796 q) 1 1 (meaning792 q) (meaning794 q) (meaning797 q) hs
  change valuationOf q 792 = false ∨ valuationOf q 794 = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 792 = false ∨ valuation q 794 = false ∨ valuation q 797 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 792 = false ∨ valuationOf q 795 = false ∨ valuationOf q 798 = true := by
  have hs : count796 q = (countLit q [-6, -7]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (792)) (literal (valuationOf q) (795)) (literal (valuationOf q) (798)) (countLit q [-6, -7]) (countLit q [-11, -12]) (count796 q) 1 2 (meaning792 q) (meaning795 q) (meaning798 q) hs
  change valuationOf q 792 = false ∨ valuationOf q 795 = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 792 = false ∨ valuation q 795 = false ∨ valuation q 798 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 793 = false ∨ valuationOf q 797 = true := by
  have hs : count796 q = (countLit q [-6, -7]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-11, -12])
  have hm := merge_left (literal (valuationOf q) (793)) (literal (valuationOf q) (797)) (countLit q [-6, -7]) (countLit q [-11, -12]) (count796 q) 2 (meaning793 q) (meaning797 q) hs
  change valuationOf q 793 = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 793 = false ∨ valuation q 797 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 793 = false ∨ valuationOf q 794 = false ∨ valuationOf q 798 = true := by
  have hs : count796 q = (countLit q [-6, -7]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (793)) (literal (valuationOf q) (794)) (literal (valuationOf q) (798)) (countLit q [-6, -7]) (countLit q [-11, -12]) (count796 q) 2 1 (meaning793 q) (meaning794 q) (meaning798 q) hs
  change valuationOf q 793 = false ∨ valuationOf q 794 = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 793 = false ∨ valuation q 794 = false ∨ valuation q 798 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 793 = false ∨ valuationOf q 795 = false ∨ valuationOf q 799 = true := by
  have hs : count796 q = (countLit q [-6, -7]) + (countLit q [-11, -12]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-11, -12])
  have hm := merge_two (literal (valuationOf q) (793)) (literal (valuationOf q) (795)) (literal (valuationOf q) (799)) (countLit q [-6, -7]) (countLit q [-11, -12]) (count796 q) 2 2 (meaning793 q) (meaning795 q) (meaning799 q) hs
  change valuationOf q 793 = false ∨ valuationOf q 795 = false ∨ valuationOf q 799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 793 = false ∨ valuation q 795 = false ∨ valuation q 799 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 796 = false ∨ valuationOf q 800 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_right (literal (valuationOf q) (796)) (literal (valuationOf q) (800)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 1 (meaning796 q) (meaning800 q) hs
  change valuationOf q 796 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 796 = false ∨ valuation q 800 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 797 = false ∨ valuationOf q 801 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_right (literal (valuationOf q) (797)) (literal (valuationOf q) (801)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 2 (meaning797 q) (meaning801 q) hs
  change valuationOf q 797 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 797 = false ∨ valuation q 801 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 798 = false ∨ valuationOf q 802 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_right (literal (valuationOf q) (798)) (literal (valuationOf q) (802)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 3 (meaning798 q) (meaning802 q) hs
  change valuationOf q 798 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 798 = false ∨ valuation q 802 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 803 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_right (literal (valuationOf q) (799)) (literal (valuationOf q) (803)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 4 (meaning799 q) (meaning803 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 803 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 800 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_left (literal (valuationOf q) (789)) (literal (valuationOf q) (800)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 1 (meaning789 q) (meaning800 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 800 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 796 = false ∨ valuationOf q 801 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (796)) (literal (valuationOf q) (801)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 1 1 (meaning789 q) (meaning796 q) (meaning801 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 796 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 796 = false ∨ valuation q 801 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 797 = false ∨ valuationOf q 802 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (797)) (literal (valuationOf q) (802)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 1 2 (meaning789 q) (meaning797 q) (meaning802 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 797 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 797 = false ∨ valuation q 802 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 798 = false ∨ valuationOf q 803 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (798)) (literal (valuationOf q) (803)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 1 3 (meaning789 q) (meaning798 q) (meaning803 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 798 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 798 = false ∨ valuation q 803 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 799 = false ∨ valuationOf q 804 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (799)) (literal (valuationOf q) (804)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 1 4 (meaning789 q) (meaning799 q) (meaning804 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 799 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 799 = false ∨ valuation q 804 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 801 = true := by
  have hs : count800 q = (countLit q [-1, -2, -4]) + (countLit q [-6, -7, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4]) (l₂ := [-6, -7, -11, -12])
  have hm := merge_left (literal (valuationOf q) (790)) (literal (valuationOf q) (801)) (countLit q [-1, -2, -4]) (countLit q [-6, -7, -11, -12]) (count800 q) 2 (meaning790 q) (meaning801 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 801 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E257.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112257
