import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec51 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1633 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1075 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1065)) (literal (valuationOf q) (1075)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 2 7 (meaning1036 q) (meaning1065 q) (meaning1075 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1633 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1065 = false ∨ valuation q 1075 = true := counterClause1633 (baseVal q)

theorem counterClause1634 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1066 = false ∨ valuationOf q 1076 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1066)) (literal (valuationOf q) (1076)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 2 8 (meaning1036 q) (meaning1066 q) (meaning1076 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1066 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1634 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1066 = false ∨ valuation q 1076 = true := counterClause1634 (baseVal q)

theorem counterClause1635 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1072 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1061)) (literal (valuationOf q) (1072)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 3 3 (meaning1037 q) (meaning1061 q) (meaning1072 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1072 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1635 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1061 = false ∨ valuation q 1072 = true := counterClause1635 (baseVal q)

theorem counterClause1636 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1073 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1062)) (literal (valuationOf q) (1073)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 3 4 (meaning1037 q) (meaning1062 q) (meaning1073 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1073 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1636 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1062 = false ∨ valuation q 1073 = true := counterClause1636 (baseVal q)

theorem counterClause1637 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1074 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1063)) (literal (valuationOf q) (1074)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 3 5 (meaning1037 q) (meaning1063 q) (meaning1074 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1074 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1637 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1063 = false ∨ valuation q 1074 = true := counterClause1637 (baseVal q)

theorem counterClause1638 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1064 = false ∨ valuationOf q 1075 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1064)) (literal (valuationOf q) (1075)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 3 6 (meaning1037 q) (meaning1064 q) (meaning1075 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1064 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1638 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1064 = false ∨ valuation q 1075 = true := counterClause1638 (baseVal q)

theorem counterClause1639 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1076 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1065)) (literal (valuationOf q) (1076)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 3 7 (meaning1037 q) (meaning1065 q) (meaning1076 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1639 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1065 = false ∨ valuation q 1076 = true := counterClause1639 (baseVal q)

theorem counterClause1640 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1066 = false ∨ valuationOf q 1077 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1066)) (literal (valuationOf q) (1077)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 3 8 (meaning1037 q) (meaning1066 q) (meaning1077 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1066 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1640 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1066 = false ∨ valuation q 1077 = true := counterClause1640 (baseVal q)

theorem counterClause1641 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1071 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1071)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 4 1 (meaning1038 q) (meaning1059 q) (meaning1071 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1071 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1641 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1059 = false ∨ valuation q 1071 = true := counterClause1641 (baseVal q)

theorem counterClause1642 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1072 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1072)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 4 2 (meaning1038 q) (meaning1060 q) (meaning1072 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1072 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1642 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1060 = false ∨ valuation q 1072 = true := counterClause1642 (baseVal q)

theorem counterClause1643 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1073 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1061)) (literal (valuationOf q) (1073)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 4 3 (meaning1038 q) (meaning1061 q) (meaning1073 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1073 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1643 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1061 = false ∨ valuation q 1073 = true := counterClause1643 (baseVal q)

theorem counterClause1644 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1074 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1062)) (literal (valuationOf q) (1074)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 4 4 (meaning1038 q) (meaning1062 q) (meaning1074 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1074 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1644 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1062 = false ∨ valuation q 1074 = true := counterClause1644 (baseVal q)

theorem counterClause1645 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1075 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1063)) (literal (valuationOf q) (1075)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 4 5 (meaning1038 q) (meaning1063 q) (meaning1075 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1645 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1063 = false ∨ valuation q 1075 = true := counterClause1645 (baseVal q)

theorem counterClause1646 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1064 = false ∨ valuationOf q 1076 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1064)) (literal (valuationOf q) (1076)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 4 6 (meaning1038 q) (meaning1064 q) (meaning1076 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1064 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1646 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1064 = false ∨ valuation q 1076 = true := counterClause1646 (baseVal q)

theorem counterClause1647 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1077 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1065)) (literal (valuationOf q) (1077)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 4 7 (meaning1038 q) (meaning1065 q) (meaning1077 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1647 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1065 = false ∨ valuation q 1077 = true := counterClause1647 (baseVal q)

theorem counterClause1648 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1066 = false ∨ valuationOf q 1078 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1066)) (literal (valuationOf q) (1078)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 4 8 (meaning1038 q) (meaning1066 q) (meaning1078 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1066 = false ∨ valuationOf q 1078 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1648 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1066 = false ∨ valuation q 1078 = true := counterClause1648 (baseVal q)

theorem counterClause1649 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1072 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1072)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 5 1 (meaning1039 q) (meaning1059 q) (meaning1072 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1072 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1649 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1059 = false ∨ valuation q 1072 = true := counterClause1649 (baseVal q)

theorem counterClause1650 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1073 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1073)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 5 2 (meaning1039 q) (meaning1060 q) (meaning1073 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1073 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1650 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1060 = false ∨ valuation q 1073 = true := counterClause1650 (baseVal q)

theorem counterClause1651 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1074 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1061)) (literal (valuationOf q) (1074)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 5 3 (meaning1039 q) (meaning1061 q) (meaning1074 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1074 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1651 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1061 = false ∨ valuation q 1074 = true := counterClause1651 (baseVal q)

theorem counterClause1652 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1075 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1062)) (literal (valuationOf q) (1075)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 5 4 (meaning1039 q) (meaning1062 q) (meaning1075 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1652 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1062 = false ∨ valuation q 1075 = true := counterClause1652 (baseVal q)

theorem counterClause1653 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1076 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1063)) (literal (valuationOf q) (1076)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 5 5 (meaning1039 q) (meaning1063 q) (meaning1076 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1653 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1063 = false ∨ valuation q 1076 = true := counterClause1653 (baseVal q)

theorem counterClause1654 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1064 = false ∨ valuationOf q 1077 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1064)) (literal (valuationOf q) (1077)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 5 6 (meaning1039 q) (meaning1064 q) (meaning1077 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1064 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1654 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1064 = false ∨ valuation q 1077 = true := counterClause1654 (baseVal q)

theorem counterClause1655 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1078 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1065)) (literal (valuationOf q) (1078)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 5 7 (meaning1039 q) (meaning1065 q) (meaning1078 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1078 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1655 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1065 = false ∨ valuation q 1078 = true := counterClause1655 (baseVal q)

theorem counterClause1656 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1066 = false ∨ valuationOf q 1079 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1066)) (literal (valuationOf q) (1079)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 5 8 (meaning1039 q) (meaning1066 q) (meaning1079 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1066 = false ∨ valuationOf q 1079 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1656 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1066 = false ∨ valuation q 1079 = true := counterClause1656 (baseVal q)

theorem counterClause1657 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1073 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1073)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 6 1 (meaning1040 q) (meaning1059 q) (meaning1073 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1073 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1657 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1059 = false ∨ valuation q 1073 = true := counterClause1657 (baseVal q)

theorem counterClause1658 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1074 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1060)) (literal (valuationOf q) (1074)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 6 2 (meaning1040 q) (meaning1060 q) (meaning1074 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1060 = false ∨ valuationOf q 1074 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1658 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1060 = false ∨ valuation q 1074 = true := counterClause1658 (baseVal q)

theorem counterClause1659 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1075 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1061)) (literal (valuationOf q) (1075)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 6 3 (meaning1040 q) (meaning1061 q) (meaning1075 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1061 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1659 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1061 = false ∨ valuation q 1075 = true := counterClause1659 (baseVal q)

theorem counterClause1660 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1076 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1062)) (literal (valuationOf q) (1076)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 6 4 (meaning1040 q) (meaning1062 q) (meaning1076 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1062 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1660 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1062 = false ∨ valuation q 1076 = true := counterClause1660 (baseVal q)

theorem counterClause1661 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1077 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1063)) (literal (valuationOf q) (1077)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 6 5 (meaning1040 q) (meaning1063 q) (meaning1077 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1063 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1661 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1063 = false ∨ valuation q 1077 = true := counterClause1661 (baseVal q)

theorem counterClause1662 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1064 = false ∨ valuationOf q 1078 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1064)) (literal (valuationOf q) (1078)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 6 6 (meaning1040 q) (meaning1064 q) (meaning1078 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1064 = false ∨ valuationOf q 1078 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1662 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1064 = false ∨ valuation q 1078 = true := counterClause1662 (baseVal q)

theorem counterClause1663 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1079 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1065)) (literal (valuationOf q) (1079)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 6 7 (meaning1040 q) (meaning1065 q) (meaning1079 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1079 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1663 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1065 = false ∨ valuation q 1079 = true := counterClause1663 (baseVal q)

theorem counterClause1664 (q : Nat → Bool) : valuationOf q 1041 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1074 = true := by
  have hs : count1067 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) + (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79]) (l₂ := [-82, -83, -86, -87, -89, -90, -91, -94])
  have hm := merge_two (literal (valuationOf q) (1041)) (literal (valuationOf q) (1059)) (literal (valuationOf q) (1074)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79]) (countLit q [-82, -83, -86, -87, -89, -90, -91, -94]) (count1067 q) 7 1 (meaning1041 q) (meaning1059 q) (meaning1074 q) hs
  change valuationOf q 1041 = false ∨ valuationOf q 1059 = false ∨ valuationOf q 1074 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1664 (q : Snake 81) (h : Conditions q) : valuation q 1041 = false ∨ valuation q 1059 = false ∨ valuation q 1074 = true := counterClause1664 (baseVal q)

theorem block51 (q : Snake 81) (h : Conditions q) : B112E057.Block51 (valuation q) :=
  ⟨clause1633 q h, clause1634 q h, clause1635 q h, clause1636 q h, clause1637 q h, clause1638 q h, clause1639 q h, clause1640 q h, clause1641 q h, clause1642 q h, clause1643 q h, clause1644 q h, clause1645 q h, clause1646 q h, clause1647 q h, clause1648 q h, clause1649 q h, clause1650 q h, clause1651 q h, clause1652 q h, clause1653 q h, clause1654 q h, clause1655 q h, clause1656 q h, clause1657 q h, clause1658 q h, clause1659 q h, clause1660 q h, clause1661 q h, clause1662 q h, clause1663 q h, clause1664 q h⟩

end
end Snake9.Regrowth.E112057
