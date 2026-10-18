import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 826 = false ∨ valuationOf q 844 = false ∨ valuationOf q 854 = true := by
  have hs : count851 q = (countLit q [-27, -29, -30, -32, -33, -36, -39]) + (countLit q [-41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -33, -36, -39]) (l₂ := [-41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (826)) (literal (valuationOf q) (844)) (literal (valuationOf q) (854)) (countLit q [-27, -29, -30, -32, -33, -36, -39]) (countLit q [-41, -42, -45, -47, -48, -50, -51]) (count851 q) 3 1 (meaning826 q) (meaning844 q) (meaning854 q) hs
  change valuationOf q 826 = false ∨ valuationOf q 844 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 826 = false ∨ valuation q 844 = false ∨ valuation q 854 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 826 = false ∨ valuationOf q 845 = false ∨ valuationOf q 855 = true := by
  have hs : count851 q = (countLit q [-27, -29, -30, -32, -33, -36, -39]) + (countLit q [-41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -33, -36, -39]) (l₂ := [-41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (826)) (literal (valuationOf q) (845)) (literal (valuationOf q) (855)) (countLit q [-27, -29, -30, -32, -33, -36, -39]) (countLit q [-41, -42, -45, -47, -48, -50, -51]) (count851 q) 3 2 (meaning826 q) (meaning845 q) (meaning855 q) hs
  change valuationOf q 826 = false ∨ valuationOf q 845 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 826 = false ∨ valuation q 845 = false ∨ valuation q 855 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 844 = false ∨ valuationOf q 855 = true := by
  have hs : count851 q = (countLit q [-27, -29, -30, -32, -33, -36, -39]) + (countLit q [-41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -32, -33, -36, -39]) (l₂ := [-41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (844)) (literal (valuationOf q) (855)) (countLit q [-27, -29, -30, -32, -33, -36, -39]) (countLit q [-41, -42, -45, -47, -48, -50, -51]) (count851 q) 4 1 (meaning827 q) (meaning844 q) (meaning855 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 844 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 844 = false ∨ valuation q 855 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 853 = false ∨ valuationOf q 872 = true := by
  have hs : count865 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (853)) (literal (valuationOf q) (872)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (count865 q) 5 3 (meaning801 q) (meaning853 q) (meaning872 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 853 = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 853 = false ∨ valuation q 872 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 854 = false ∨ valuationOf q 873 = true := by
  have hs : count865 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (854)) (literal (valuationOf q) (873)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (count865 q) 5 4 (meaning801 q) (meaning854 q) (meaning873 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 854 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 854 = false ∨ valuation q 873 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 855 = false ∨ valuationOf q 874 = true := by
  have hs : count865 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (855)) (literal (valuationOf q) (874)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (count865 q) 5 5 (meaning801 q) (meaning855 q) (meaning874 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 855 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 855 = false ∨ valuation q 874 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 853 = false ∨ valuationOf q 873 = true := by
  have hs : count865 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (853)) (literal (valuationOf q) (873)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (count865 q) 6 3 (meaning802 q) (meaning853 q) (meaning873 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 853 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 853 = false ∨ valuation q 873 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 854 = false ∨ valuationOf q 874 = true := by
  have hs : count865 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (854)) (literal (valuationOf q) (874)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (count865 q) 6 4 (meaning802 q) (meaning854 q) (meaning874 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 854 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 854 = false ∨ valuation q 874 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 855 = false ∨ valuationOf q 875 = true := by
  have hs : count865 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (855)) (literal (valuationOf q) (875)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (count865 q) 6 5 (meaning802 q) (meaning855 q) (meaning875 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 855 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 855 = false ∨ valuation q 875 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 852 = false ∨ valuationOf q 873 = true := by
  have hs : count865 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (852)) (literal (valuationOf q) (873)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (count865 q) 7 2 (meaning803 q) (meaning852 q) (meaning873 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 852 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 852 = false ∨ valuation q 873 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 853 = false ∨ valuationOf q 874 = true := by
  have hs : count865 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (853)) (literal (valuationOf q) (874)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (count865 q) 7 3 (meaning803 q) (meaning853 q) (meaning874 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 853 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 853 = false ∨ valuation q 874 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 854 = false ∨ valuationOf q 875 = true := by
  have hs : count865 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (854)) (literal (valuationOf q) (875)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (count865 q) 7 4 (meaning803 q) (meaning854 q) (meaning875 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 854 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 854 = false ∨ valuation q 875 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 853 = false ∨ valuationOf q 875 = true := by
  have hs : count865 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (853)) (literal (valuationOf q) (875)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (count865 q) 8 3 (meaning804 q) (meaning853 q) (meaning875 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 853 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 853 = false ∨ valuation q 875 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 854 = false ∨ valuationOf q 876 = true := by
  have hs : count865 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (854)) (literal (valuationOf q) (876)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (count865 q) 8 4 (meaning804 q) (meaning854 q) (meaning876 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 854 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 854 = false ∨ valuation q 876 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 854 = false ∨ valuationOf q 877 = true := by
  have hs : count865 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (805)) (literal (valuationOf q) (854)) (literal (valuationOf q) (877)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -30, -32, -33, -36, -39, -41, -42, -45, -47, -48, -50, -51]) (count865 q) 9 4 (meaning805 q) (meaning854 q) (meaning877 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 854 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 854 = false ∨ valuation q 877 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 882 = true := by
  have hs : count882 q = (countLit q [-57]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (882)) (countLit q [-57]) (countLit q [-60]) (count882 q) 1 (meaningNeg60 q) (meaning882 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 882 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 884 = true := by
  have hs : count884 q = (countLit q [-55]) + (countLit q [-57, -60]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57, -60])
  have hm := merge_right (literal (valuationOf q) (882)) (literal (valuationOf q) (884)) (countLit q [-55]) (countLit q [-57, -60]) (count884 q) 1 (meaning882 q) (meaning884 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 884 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 884 = true := by
  have hs : count884 q = (countLit q [-55]) + (countLit q [-57, -60]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57, -60])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (884)) (countLit q [-55]) (countLit q [-57, -60]) (count884 q) 1 (meaningNeg55 q) (meaning884 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 884 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 887 = true := by
  have hs : count887 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (887)) (countLit q [-62]) (countLit q [-63]) (count887 q) 1 (meaningNeg63 q) (meaning887 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 887 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 887 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 889 = true := by
  have hs : count889 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (889)) (countLit q [-65]) (countLit q [-68]) (count889 q) 1 (meaningNeg68 q) (meaning889 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 889 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 889 = true := by
  have hs : count889 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (889)) (countLit q [-65]) (countLit q [-68]) (count889 q) 1 (meaningNeg65 q) (meaning889 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 889 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 889 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 68 = true ∨ valuationOf q 890 = true := by
  have hs : count889 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (890)) (countLit q [-65]) (countLit q [-68]) (count889 q) 1 1 (meaningNeg65 q) (meaningNeg68 q) (meaning890 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 890 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 68 = true ∨ valuation q 890 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 891 = true := by
  have hs : count891 q = (countLit q [-62, -63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-62, -63]) (l₂ := [-65, -68])
  have hm := merge_right (literal (valuationOf q) (889)) (literal (valuationOf q) (891)) (countLit q [-62, -63]) (countLit q [-65, -68]) (count891 q) 1 (meaning889 q) (meaning891 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 891 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 892 = true := by
  have hs : count891 q = (countLit q [-62, -63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-62, -63]) (l₂ := [-65, -68])
  have hm := merge_right (literal (valuationOf q) (890)) (literal (valuationOf q) (892)) (countLit q [-62, -63]) (countLit q [-65, -68]) (count891 q) 2 (meaning890 q) (meaning892 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 892 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 891 = true := by
  have hs : count891 q = (countLit q [-62, -63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-62, -63]) (l₂ := [-65, -68])
  have hm := merge_left (literal (valuationOf q) (887)) (literal (valuationOf q) (891)) (countLit q [-62, -63]) (countLit q [-65, -68]) (count891 q) 1 (meaning887 q) (meaning891 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 891 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 891 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 889 = false ∨ valuationOf q 892 = true := by
  have hs : count891 q = (countLit q [-62, -63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-62, -63]) (l₂ := [-65, -68])
  have hm := merge_two (literal (valuationOf q) (887)) (literal (valuationOf q) (889)) (literal (valuationOf q) (892)) (countLit q [-62, -63]) (countLit q [-65, -68]) (count891 q) 1 1 (meaning887 q) (meaning889 q) (meaning892 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 889 = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 889 = false ∨ valuation q 892 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 887 = false ∨ valuationOf q 890 = false ∨ valuationOf q 893 = true := by
  have hs : count891 q = (countLit q [-62, -63]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-62, -63]) (l₂ := [-65, -68])
  have hm := merge_two (literal (valuationOf q) (887)) (literal (valuationOf q) (890)) (literal (valuationOf q) (893)) (countLit q [-62, -63]) (countLit q [-65, -68]) (count891 q) 1 2 (meaning887 q) (meaning890 q) (meaning893 q) hs
  change valuationOf q 887 = false ∨ valuationOf q 890 = false ∨ valuationOf q 893 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 887 = false ∨ valuation q 890 = false ∨ valuation q 893 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 895 = true := by
  have hs : count895 q = (countLit q [-55, -57, -60]) + (countLit q [-62, -63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60]) (l₂ := [-62, -63, -65, -68])
  have hm := merge_right (literal (valuationOf q) (891)) (literal (valuationOf q) (895)) (countLit q [-55, -57, -60]) (countLit q [-62, -63, -65, -68]) (count895 q) 1 (meaning891 q) (meaning895 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 895 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 892 = false ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-55, -57, -60]) + (countLit q [-62, -63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60]) (l₂ := [-62, -63, -65, -68])
  have hm := merge_right (literal (valuationOf q) (892)) (literal (valuationOf q) (896)) (countLit q [-55, -57, -60]) (countLit q [-62, -63, -65, -68]) (count895 q) 2 (meaning892 q) (meaning896 q) hs
  change valuationOf q 892 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 892 = false ∨ valuation q 896 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 893 = false ∨ valuationOf q 897 = true := by
  have hs : count895 q = (countLit q [-55, -57, -60]) + (countLit q [-62, -63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60]) (l₂ := [-62, -63, -65, -68])
  have hm := merge_right (literal (valuationOf q) (893)) (literal (valuationOf q) (897)) (countLit q [-55, -57, -60]) (countLit q [-62, -63, -65, -68]) (count895 q) 3 (meaning893 q) (meaning897 q) hs
  change valuationOf q 893 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 893 = false ∨ valuation q 897 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 891 = false ∨ valuationOf q 896 = true := by
  have hs : count895 q = (countLit q [-55, -57, -60]) + (countLit q [-62, -63, -65, -68]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -60]) (l₂ := [-62, -63, -65, -68])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (891)) (literal (valuationOf q) (896)) (countLit q [-55, -57, -60]) (countLit q [-62, -63, -65, -68]) (count895 q) 1 1 (meaning884 q) (meaning891 q) (meaning896 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 891 = false ∨ valuationOf q 896 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 891 = false ∨ valuation q 896 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 902 = true := by
  have hs : count902 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (902)) (countLit q [-71]) (countLit q [-73]) (count902 q) 1 (meaningNeg73 q) (meaning902 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 902 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 902 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E123.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112123
