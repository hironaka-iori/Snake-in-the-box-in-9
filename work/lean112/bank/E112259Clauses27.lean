import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 797 = false ∨ valuationOf q 801 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_right (literal (valuationOf q) (797)) (literal (valuationOf q) (801)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 2 (meaning797 q) (meaning801 q) hs
  change valuationOf q 797 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 797 = false ∨ valuation q 801 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 798 = false ∨ valuationOf q 802 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_right (literal (valuationOf q) (798)) (literal (valuationOf q) (802)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 3 (meaning798 q) (meaning802 q) hs
  change valuationOf q 798 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 798 = false ∨ valuation q 802 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 803 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_right (literal (valuationOf q) (799)) (literal (valuationOf q) (803)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 4 (meaning799 q) (meaning803 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 803 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 800 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_left (literal (valuationOf q) (789)) (literal (valuationOf q) (800)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 1 (meaning789 q) (meaning800 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 800 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 796 = false ∨ valuationOf q 801 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (796)) (literal (valuationOf q) (801)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 1 1 (meaning789 q) (meaning796 q) (meaning801 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 796 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 796 = false ∨ valuation q 801 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 797 = false ∨ valuationOf q 802 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (797)) (literal (valuationOf q) (802)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 1 2 (meaning789 q) (meaning797 q) (meaning802 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 797 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 797 = false ∨ valuation q 802 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 798 = false ∨ valuationOf q 803 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (798)) (literal (valuationOf q) (803)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 1 3 (meaning789 q) (meaning798 q) (meaning803 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 798 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 798 = false ∨ valuation q 803 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 799 = false ∨ valuationOf q 804 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (799)) (literal (valuationOf q) (804)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 1 4 (meaning789 q) (meaning799 q) (meaning804 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 799 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 799 = false ∨ valuation q 804 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 801 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_left (literal (valuationOf q) (790)) (literal (valuationOf q) (801)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 2 (meaning790 q) (meaning801 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 801 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 796 = false ∨ valuationOf q 802 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (796)) (literal (valuationOf q) (802)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 2 1 (meaning790 q) (meaning796 q) (meaning802 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 796 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 796 = false ∨ valuation q 802 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 797 = false ∨ valuationOf q 803 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (797)) (literal (valuationOf q) (803)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 2 2 (meaning790 q) (meaning797 q) (meaning803 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 797 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 797 = false ∨ valuation q 803 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 798 = false ∨ valuationOf q 804 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (798)) (literal (valuationOf q) (804)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 2 3 (meaning790 q) (meaning798 q) (meaning804 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 798 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 798 = false ∨ valuation q 804 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 799 = false ∨ valuationOf q 805 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (799)) (literal (valuationOf q) (805)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 2 4 (meaning790 q) (meaning799 q) (meaning805 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 799 = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 799 = false ∨ valuation q 805 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 791 = false ∨ valuationOf q 802 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_left (literal (valuationOf q) (791)) (literal (valuationOf q) (802)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 3 (meaning791 q) (meaning802 q) hs
  change valuationOf q 791 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 791 = false ∨ valuation q 802 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 791 = false ∨ valuationOf q 796 = false ∨ valuationOf q 803 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (791)) (literal (valuationOf q) (796)) (literal (valuationOf q) (803)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 3 1 (meaning791 q) (meaning796 q) (meaning803 q) hs
  change valuationOf q 791 = false ∨ valuationOf q 796 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 791 = false ∨ valuation q 796 = false ∨ valuation q 803 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 791 = false ∨ valuationOf q 797 = false ∨ valuationOf q 804 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (791)) (literal (valuationOf q) (797)) (literal (valuationOf q) (804)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 3 2 (meaning791 q) (meaning797 q) (meaning804 q) hs
  change valuationOf q 791 = false ∨ valuationOf q 797 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 791 = false ∨ valuation q 797 = false ∨ valuation q 804 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 791 = false ∨ valuationOf q 798 = false ∨ valuationOf q 805 = true := by
  have hs : count800 q = (countLit q [-1, -2, -6]) + (countLit q [-7, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6]) (l₂ := [-7, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (791)) (literal (valuationOf q) (798)) (literal (valuationOf q) (805)) (countLit q [-1, -2, -6]) (countLit q [-7, -10, -11, -14]) (count800 q) 3 3 (meaning791 q) (meaning798 q) (meaning805 q) hs
  change valuationOf q 791 = false ∨ valuationOf q 798 = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 791 = false ∨ valuation q 798 = false ∨ valuation q 805 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 807 = true := by
  have hs : count807 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (807)) (countLit q [-17]) (countLit q [-19]) (count807 q) 1 (meaningNeg19 q) (meaning807 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 807 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 807 = true := by
  have hs : count807 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (807)) (countLit q [-17]) (countLit q [-19]) (count807 q) 1 (meaningNeg17 q) (meaning807 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 807 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 19 = true ∨ valuationOf q 808 = true := by
  have hs : count807 q = (countLit q [-17]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (808)) (countLit q [-17]) (countLit q [-19]) (count807 q) 1 1 (meaningNeg17 q) (meaningNeg19 q) (meaning808 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 19 = true ∨ valuation q 808 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 807 = false ∨ valuationOf q 809 = true := by
  have hs : count809 q = (countLit q [-15]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -19])
  have hm := merge_right (literal (valuationOf q) (807)) (literal (valuationOf q) (809)) (countLit q [-15]) (countLit q [-17, -19]) (count809 q) 1 (meaning807 q) (meaning809 q) hs
  change valuationOf q 807 = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 807 = false ∨ valuation q 809 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 808 = false ∨ valuationOf q 810 = true := by
  have hs : count809 q = (countLit q [-15]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -19])
  have hm := merge_right (literal (valuationOf q) (808)) (literal (valuationOf q) (810)) (countLit q [-15]) (countLit q [-17, -19]) (count809 q) 2 (meaning808 q) (meaning810 q) hs
  change valuationOf q 808 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 808 = false ∨ valuation q 810 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 809 = true := by
  have hs : count809 q = (countLit q [-15]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -19])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (809)) (countLit q [-15]) (countLit q [-17, -19]) (count809 q) 1 (meaningNeg15 q) (meaning809 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 809 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 807 = false ∨ valuationOf q 810 = true := by
  have hs : count809 q = (countLit q [-15]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -19])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (807)) (literal (valuationOf q) (810)) (countLit q [-15]) (countLit q [-17, -19]) (count809 q) 1 1 (meaningNeg15 q) (meaning807 q) (meaning810 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 807 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 807 = false ∨ valuation q 810 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 808 = false ∨ valuationOf q 811 = true := by
  have hs : count809 q = (countLit q [-15]) + (countLit q [-17, -19]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -19])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (808)) (literal (valuationOf q) (811)) (countLit q [-15]) (countLit q [-17, -19]) (count809 q) 1 2 (meaningNeg15 q) (meaning808 q) (meaning811 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 808 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 808 = false ∨ valuation q 811 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 812 = true := by
  have hs : count812 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (812)) (countLit q [-21]) (countLit q [-23]) (count812 q) 1 (meaningNeg23 q) (meaning812 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 812 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 812 = true := by
  have hs : count812 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (812)) (countLit q [-21]) (countLit q [-23]) (count812 q) 1 (meaningNeg21 q) (meaning812 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 812 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 23 = true ∨ valuationOf q 813 = true := by
  have hs : count812 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (813)) (countLit q [-21]) (countLit q [-23]) (count812 q) 1 1 (meaningNeg21 q) (meaningNeg23 q) (meaning813 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 813 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 23 = true ∨ valuation q 813 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 814 = true := by
  have hs : count814 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_right (literal (valuationOf q) (-27)) (literal (valuationOf q) (814)) (countLit q [-25]) (countLit q [-27]) (count814 q) 1 (meaningNeg27 q) (meaning814 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 814 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 814 = true := by
  have hs : count814 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (814)) (countLit q [-25]) (countLit q [-27]) (count814 q) 1 (meaningNeg25 q) (meaning814 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 814 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 27 = true ∨ valuationOf q 815 = true := by
  have hs : count814 q = (countLit q [-25]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-27])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-27)) (literal (valuationOf q) (815)) (countLit q [-25]) (countLit q [-27]) (count814 q) 1 1 (meaningNeg25 q) (meaningNeg27 q) (meaning815 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 27)) = false ∨ valuationOf q 815 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 27 = true ∨ valuation q 815 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 816 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-25, -27])
  have hm := merge_right (literal (valuationOf q) (814)) (literal (valuationOf q) (816)) (countLit q [-21, -23]) (countLit q [-25, -27]) (count816 q) 1 (meaning814 q) (meaning816 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 816 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E259.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112259
