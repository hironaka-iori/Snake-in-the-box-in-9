import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1015 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1015)) (literal (valuationOf q) (1027)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 4 (meaning1015 q) (meaning1027 q) hs
  change valuationOf q 1015 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1015 = false ∨ valuation q 1027 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1015 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1015)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1028)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 4 1 (meaning1015 q) (meaning1020 q) (meaning1028 q) hs
  change valuationOf q 1015 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1015 = false ∨ valuation q 1020 = false ∨ valuation q 1028 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1015 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1029 = true := by
  have hs : count1024 q = (countLit q [-80, -81, -82, -86]) + (countLit q [-87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -81, -82, -86]) (l₂ := [-87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1015)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1029)) (countLit q [-80, -81, -82, -86]) (countLit q [-87, -88, -91, -93]) (count1024 q) 4 2 (meaning1015 q) (meaning1021 q) (meaning1029 q) hs
  change valuationOf q 1015 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1015 = false ∨ valuation q 1021 = false ∨ valuation q 1029 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1032 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1024)) (literal (valuationOf q) (1032)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 1 (meaning1024 q) (meaning1032 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1032 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1025 = false ∨ valuationOf q 1033 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1025)) (literal (valuationOf q) (1033)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 2 (meaning1025 q) (meaning1033 q) hs
  change valuationOf q 1025 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1025 = false ∨ valuation q 1033 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1026 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1026)) (literal (valuationOf q) (1034)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 3 (meaning1026 q) (meaning1034 q) hs
  change valuationOf q 1026 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1026 = false ∨ valuation q 1034 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1027 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1027)) (literal (valuationOf q) (1035)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 4 (meaning1027 q) (meaning1035 q) hs
  change valuationOf q 1027 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1027 = false ∨ valuation q 1035 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1028 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1028)) (literal (valuationOf q) (1036)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 5 (meaning1028 q) (meaning1036 q) hs
  change valuationOf q 1028 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1028 = false ∨ valuation q 1036 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1029 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_right (literal (valuationOf q) (1029)) (literal (valuationOf q) (1037)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 6 (meaning1029 q) (meaning1037 q) hs
  change valuationOf q 1029 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1029 = false ∨ valuation q 1037 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1032 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1001)) (literal (valuationOf q) (1032)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 1 (meaning1001 q) (meaning1032 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1032 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1033 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1033)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 1 1 (meaning1001 q) (meaning1024 q) (meaning1033 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1024 = false ∨ valuation q 1033 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1034)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 1 2 (meaning1001 q) (meaning1025 q) (meaning1034 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1025 = false ∨ valuation q 1034 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1035)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 1 3 (meaning1001 q) (meaning1026 q) (meaning1035 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1026 = false ∨ valuation q 1035 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1036)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 1 4 (meaning1001 q) (meaning1027 q) (meaning1036 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1027 = false ∨ valuation q 1036 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1037)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 1 5 (meaning1001 q) (meaning1028 q) (meaning1037 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1028 = false ∨ valuation q 1037 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1038)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 1 6 (meaning1001 q) (meaning1029 q) (meaning1038 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1029 = false ∨ valuation q 1038 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1039 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1030)) (literal (valuationOf q) (1039)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 1 7 (meaning1001 q) (meaning1030 q) (meaning1039 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1030 = false ∨ valuation q 1039 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1033 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1002)) (literal (valuationOf q) (1033)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 2 (meaning1002 q) (meaning1033 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1033 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1034)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 2 1 (meaning1002 q) (meaning1024 q) (meaning1034 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1024 = false ∨ valuation q 1034 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1035)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 2 2 (meaning1002 q) (meaning1025 q) (meaning1035 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1025 = false ∨ valuation q 1035 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1036)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 2 3 (meaning1002 q) (meaning1026 q) (meaning1036 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1026 = false ∨ valuation q 1036 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1037)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 2 4 (meaning1002 q) (meaning1027 q) (meaning1037 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1027 = false ∨ valuation q 1037 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1038)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 2 5 (meaning1002 q) (meaning1028 q) (meaning1038 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1028 = false ∨ valuation q 1038 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1039 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1039)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 2 6 (meaning1002 q) (meaning1029 q) (meaning1039 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1029 = false ∨ valuation q 1039 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1003)) (literal (valuationOf q) (1034)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 3 (meaning1003 q) (meaning1034 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1034 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1035)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 3 1 (meaning1003 q) (meaning1024 q) (meaning1035 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1024 = false ∨ valuation q 1035 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1036)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 3 2 (meaning1003 q) (meaning1025 q) (meaning1036 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1025 = false ∨ valuation q 1036 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1037)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 3 3 (meaning1003 q) (meaning1026 q) (meaning1037 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1026 = false ∨ valuation q 1037 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1038)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 3 4 (meaning1003 q) (meaning1027 q) (meaning1038 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1027 = false ∨ valuation q 1038 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1039 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1039)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 3 5 (meaning1003 q) (meaning1028 q) (meaning1039 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1028 = false ∨ valuation q 1039 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1040 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1040)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 3 6 (meaning1003 q) (meaning1029 q) (meaning1040 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1029 = false ∨ valuation q 1040 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1004)) (literal (valuationOf q) (1035)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 4 (meaning1004 q) (meaning1035 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1035 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E153.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112153
