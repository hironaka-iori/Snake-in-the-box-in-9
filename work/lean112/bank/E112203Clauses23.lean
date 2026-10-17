import E112203Semantics
import B112E203Inputs
namespace Snake9.Regrowth.E112203
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 799 = true := by
  have hs : count799 q = (countLit q [-1]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -7])
  have hm := merge_left (literal (valuationOf q) (-1)) (literal (valuationOf q) (799)) (countLit q [-1]) (countLit q [-3, -7]) (count799 q) 1 (meaningNeg1 q) (meaning799 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 799 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 799 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 797 = false ∨ valuationOf q 800 = true := by
  have hs : count799 q = (countLit q [-1]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -7])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (797)) (literal (valuationOf q) (800)) (countLit q [-1]) (countLit q [-3, -7]) (count799 q) 1 1 (meaningNeg1 q) (meaning797 q) (meaning800 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 797 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 797 = false ∨ valuation q 800 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 1 = true ∨ valuationOf q 798 = false ∨ valuationOf q 801 = true := by
  have hs : count799 q = (countLit q [-1]) + (countLit q [-3, -7]) := List.countP_append (p := literal q) (l₁ := [-1]) (l₂ := [-3, -7])
  have hm := merge_two (literal (valuationOf q) (-1)) (literal (valuationOf q) (798)) (literal (valuationOf q) (801)) (countLit q [-1]) (countLit q [-3, -7]) (count799 q) 1 2 (meaningNeg1 q) (meaning798 q) (meaning801 q) hs
  change (! (valuationOf q 1)) = false ∨ valuationOf q 798 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 1 = true ∨ valuation q 798 = false ∨ valuation q 801 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 802 = true := by
  have hs : count802 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_right (literal (valuationOf q) (-9)) (literal (valuationOf q) (802)) (countLit q [-8]) (countLit q [-9]) (count802 q) 1 (meaningNeg9 q) (meaning802 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 802 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 802 = true := by
  have hs : count802 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_left (literal (valuationOf q) (-8)) (literal (valuationOf q) (802)) (countLit q [-8]) (countLit q [-9]) (count802 q) 1 (meaningNeg8 q) (meaning802 q) hs
  change (! (valuationOf q 8)) = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 802 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 9 = true ∨ valuationOf q 803 = true := by
  have hs : count802 q = (countLit q [-8]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-9])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-9)) (literal (valuationOf q) (803)) (countLit q [-8]) (countLit q [-9]) (count802 q) 1 1 (meaningNeg8 q) (meaningNeg9 q) (meaning803 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 9)) = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 9 = true ∨ valuation q 803 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 804 = true := by
  have hs : count804 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_right (literal (valuationOf q) (-14)) (literal (valuationOf q) (804)) (countLit q [-13]) (countLit q [-14]) (count804 q) 1 (meaningNeg14 q) (meaning804 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 804 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 804 = true := by
  have hs : count804 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (804)) (countLit q [-13]) (countLit q [-14]) (count804 q) 1 (meaningNeg13 q) (meaning804 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 804 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 14 = true ∨ valuationOf q 805 = true := by
  have hs : count804 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-14)) (literal (valuationOf q) (805)) (countLit q [-13]) (countLit q [-14]) (count804 q) 1 1 (meaningNeg13 q) (meaningNeg14 q) (meaning805 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 14)) = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 14 = true ∨ valuation q 805 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 806 = true := by
  have hs : count806 q = (countLit q [-8, -9]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-13, -14])
  have hm := merge_right (literal (valuationOf q) (804)) (literal (valuationOf q) (806)) (countLit q [-8, -9]) (countLit q [-13, -14]) (count806 q) 1 (meaning804 q) (meaning806 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 806 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 807 = true := by
  have hs : count806 q = (countLit q [-8, -9]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-13, -14])
  have hm := merge_right (literal (valuationOf q) (805)) (literal (valuationOf q) (807)) (countLit q [-8, -9]) (countLit q [-13, -14]) (count806 q) 2 (meaning805 q) (meaning807 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 807 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 806 = true := by
  have hs : count806 q = (countLit q [-8, -9]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-13, -14])
  have hm := merge_left (literal (valuationOf q) (802)) (literal (valuationOf q) (806)) (countLit q [-8, -9]) (countLit q [-13, -14]) (count806 q) 1 (meaning802 q) (meaning806 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 806 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 804 = false ∨ valuationOf q 807 = true := by
  have hs : count806 q = (countLit q [-8, -9]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-13, -14])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (804)) (literal (valuationOf q) (807)) (countLit q [-8, -9]) (countLit q [-13, -14]) (count806 q) 1 1 (meaning802 q) (meaning804 q) (meaning807 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 804 = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 804 = false ∨ valuation q 807 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 805 = false ∨ valuationOf q 808 = true := by
  have hs : count806 q = (countLit q [-8, -9]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-13, -14])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (805)) (literal (valuationOf q) (808)) (countLit q [-8, -9]) (countLit q [-13, -14]) (count806 q) 1 2 (meaning802 q) (meaning805 q) (meaning808 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 805 = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 805 = false ∨ valuation q 808 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 807 = true := by
  have hs : count806 q = (countLit q [-8, -9]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-13, -14])
  have hm := merge_left (literal (valuationOf q) (803)) (literal (valuationOf q) (807)) (countLit q [-8, -9]) (countLit q [-13, -14]) (count806 q) 2 (meaning803 q) (meaning807 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 807 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 806 = false ∨ valuationOf q 810 = true := by
  have hs : count810 q = (countLit q [-1, -3, -7]) + (countLit q [-8, -9, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7]) (l₂ := [-8, -9, -13, -14])
  have hm := merge_right (literal (valuationOf q) (806)) (literal (valuationOf q) (810)) (countLit q [-1, -3, -7]) (countLit q [-8, -9, -13, -14]) (count810 q) 1 (meaning806 q) (meaning810 q) hs
  change valuationOf q 806 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 806 = false ∨ valuation q 810 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 807 = false ∨ valuationOf q 811 = true := by
  have hs : count810 q = (countLit q [-1, -3, -7]) + (countLit q [-8, -9, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7]) (l₂ := [-8, -9, -13, -14])
  have hm := merge_right (literal (valuationOf q) (807)) (literal (valuationOf q) (811)) (countLit q [-1, -3, -7]) (countLit q [-8, -9, -13, -14]) (count810 q) 2 (meaning807 q) (meaning811 q) hs
  change valuationOf q 807 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 807 = false ∨ valuation q 811 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 808 = false ∨ valuationOf q 812 = true := by
  have hs : count810 q = (countLit q [-1, -3, -7]) + (countLit q [-8, -9, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7]) (l₂ := [-8, -9, -13, -14])
  have hm := merge_right (literal (valuationOf q) (808)) (literal (valuationOf q) (812)) (countLit q [-1, -3, -7]) (countLit q [-8, -9, -13, -14]) (count810 q) 3 (meaning808 q) (meaning812 q) hs
  change valuationOf q 808 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 808 = false ∨ valuation q 812 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 810 = true := by
  have hs : count810 q = (countLit q [-1, -3, -7]) + (countLit q [-8, -9, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7]) (l₂ := [-8, -9, -13, -14])
  have hm := merge_left (literal (valuationOf q) (799)) (literal (valuationOf q) (810)) (countLit q [-1, -3, -7]) (countLit q [-8, -9, -13, -14]) (count810 q) 1 (meaning799 q) (meaning810 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 810 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 806 = false ∨ valuationOf q 811 = true := by
  have hs : count810 q = (countLit q [-1, -3, -7]) + (countLit q [-8, -9, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7]) (l₂ := [-8, -9, -13, -14])
  have hm := merge_two (literal (valuationOf q) (799)) (literal (valuationOf q) (806)) (literal (valuationOf q) (811)) (countLit q [-1, -3, -7]) (countLit q [-8, -9, -13, -14]) (count810 q) 1 1 (meaning799 q) (meaning806 q) (meaning811 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 806 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 806 = false ∨ valuation q 811 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 807 = false ∨ valuationOf q 812 = true := by
  have hs : count810 q = (countLit q [-1, -3, -7]) + (countLit q [-8, -9, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7]) (l₂ := [-8, -9, -13, -14])
  have hm := merge_two (literal (valuationOf q) (799)) (literal (valuationOf q) (807)) (literal (valuationOf q) (812)) (countLit q [-1, -3, -7]) (countLit q [-8, -9, -13, -14]) (count810 q) 1 2 (meaning799 q) (meaning807 q) (meaning812 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 807 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 807 = false ∨ valuation q 812 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 808 = false ∨ valuationOf q 813 = true := by
  have hs : count810 q = (countLit q [-1, -3, -7]) + (countLit q [-8, -9, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7]) (l₂ := [-8, -9, -13, -14])
  have hm := merge_two (literal (valuationOf q) (799)) (literal (valuationOf q) (808)) (literal (valuationOf q) (813)) (countLit q [-1, -3, -7]) (countLit q [-8, -9, -13, -14]) (count810 q) 1 3 (meaning799 q) (meaning808 q) (meaning813 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 808 = false ∨ valuationOf q 813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 808 = false ∨ valuation q 813 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 811 = true := by
  have hs : count810 q = (countLit q [-1, -3, -7]) + (countLit q [-8, -9, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7]) (l₂ := [-8, -9, -13, -14])
  have hm := merge_left (literal (valuationOf q) (800)) (literal (valuationOf q) (811)) (countLit q [-1, -3, -7]) (countLit q [-8, -9, -13, -14]) (count810 q) 2 (meaning800 q) (meaning811 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 811 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 806 = false ∨ valuationOf q 812 = true := by
  have hs : count810 q = (countLit q [-1, -3, -7]) + (countLit q [-8, -9, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7]) (l₂ := [-8, -9, -13, -14])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (806)) (literal (valuationOf q) (812)) (countLit q [-1, -3, -7]) (countLit q [-8, -9, -13, -14]) (count810 q) 2 1 (meaning800 q) (meaning806 q) (meaning812 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 806 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 806 = false ∨ valuation q 812 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 807 = false ∨ valuationOf q 813 = true := by
  have hs : count810 q = (countLit q [-1, -3, -7]) + (countLit q [-8, -9, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7]) (l₂ := [-8, -9, -13, -14])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (807)) (literal (valuationOf q) (813)) (countLit q [-1, -3, -7]) (countLit q [-8, -9, -13, -14]) (count810 q) 2 2 (meaning800 q) (meaning807 q) (meaning813 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 807 = false ∨ valuationOf q 813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 807 = false ∨ valuation q 813 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 812 = true := by
  have hs : count810 q = (countLit q [-1, -3, -7]) + (countLit q [-8, -9, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7]) (l₂ := [-8, -9, -13, -14])
  have hm := merge_left (literal (valuationOf q) (801)) (literal (valuationOf q) (812)) (countLit q [-1, -3, -7]) (countLit q [-8, -9, -13, -14]) (count810 q) 3 (meaning801 q) (meaning812 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 812 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 806 = false ∨ valuationOf q 813 = true := by
  have hs : count810 q = (countLit q [-1, -3, -7]) + (countLit q [-8, -9, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7]) (l₂ := [-8, -9, -13, -14])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (806)) (literal (valuationOf q) (813)) (countLit q [-1, -3, -7]) (countLit q [-8, -9, -13, -14]) (count810 q) 3 1 (meaning801 q) (meaning806 q) (meaning813 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 806 = false ∨ valuationOf q 813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 806 = false ∨ valuation q 813 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 808 = false ∨ valuationOf q 815 = true := by
  have hs : count810 q = (countLit q [-1, -3, -7]) + (countLit q [-8, -9, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7]) (l₂ := [-8, -9, -13, -14])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (808)) (literal (valuationOf q) (815)) (countLit q [-1, -3, -7]) (countLit q [-8, -9, -13, -14]) (count810 q) 3 3 (meaning801 q) (meaning808 q) (meaning815 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 808 = false ∨ valuationOf q 815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 808 = false ∨ valuation q 815 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 817 = true := by
  have hs : count817 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (817)) (countLit q [-17]) (countLit q [-19]) (count817 q) 1 (meaningNeg19 q) (meaning817 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 817 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 817 = true := by
  have hs : count817 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (817)) (countLit q [-17]) (countLit q [-19]) (count817 q) 1 (meaningNeg17 q) (meaning817 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 817 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 19 = true ∨ valuationOf q 818 = true := by
  have hs : count817 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (818)) (countLit q [-17]) (countLit q [-19]) (count817 q) 1 1 (meaningNeg17 q) (meaningNeg19 q) (meaning818 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 818 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 819 = true := by
  have hs : count819 q = (countLit q [-16]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-17, -19])
  have hm := merge_right (literal (valuationOf q) (817)) (literal (valuationOf q) (819)) (countLit q [-16]) (countLit q [-17, -19]) (count819 q) 1 (meaning817 q) (meaning819 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 819 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E203.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112203
