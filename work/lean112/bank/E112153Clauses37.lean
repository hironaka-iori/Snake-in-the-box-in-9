import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1036)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 4 1 (meaning1004 q) (meaning1024 q) (meaning1036 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1024 = false ∨ valuation q 1036 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1037)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 4 2 (meaning1004 q) (meaning1025 q) (meaning1037 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1025 = false ∨ valuation q 1037 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1038)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 4 3 (meaning1004 q) (meaning1026 q) (meaning1038 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1026 = false ∨ valuation q 1038 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1039 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1039)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 4 4 (meaning1004 q) (meaning1027 q) (meaning1039 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1027 = false ∨ valuation q 1039 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1040 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1040)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 4 5 (meaning1004 q) (meaning1028 q) (meaning1040 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1028 = false ∨ valuation q 1040 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1005)) (literal (valuationOf q) (1036)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 5 (meaning1005 q) (meaning1036 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1036 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1037)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 5 1 (meaning1005 q) (meaning1024 q) (meaning1037 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1024 = false ∨ valuation q 1037 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1038)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 5 2 (meaning1005 q) (meaning1025 q) (meaning1038 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1025 = false ∨ valuation q 1038 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1039 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1039)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 5 3 (meaning1005 q) (meaning1026 q) (meaning1039 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1026 = false ∨ valuation q 1039 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1040 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1040)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 5 4 (meaning1005 q) (meaning1027 q) (meaning1040 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1027 = false ∨ valuation q 1040 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_left (literal (valuationOf q) (1006)) (literal (valuationOf q) (1037)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 6 (meaning1006 q) (meaning1037 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1037 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1038)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 6 1 (meaning1006 q) (meaning1024 q) (meaning1038 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1024 = false ∨ valuation q 1038 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1040 = true := by
  have hs : count1032 q = (countLit q [-63, -65, -68, -71, -73, -74, -75]) + (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75]) (l₂ := [-80, -81, -82, -86, -87, -88, -91, -93])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1040)) (countLit q [-63, -65, -68, -71, -73, -74, -75]) (countLit q [-80, -81, -82, -86, -87, -88, -91, -93]) (count1032 q) 6 3 (meaning1006 q) (meaning1026 q) (meaning1040 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1026 = false ∨ valuation q 1040 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1047 = true := by
  have hs : count1047 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1047)) (countLit q [-94]) (countLit q [-96]) (count1047 q) 1 (meaningNeg96 q) (meaning1047 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1047 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1047 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1047 = true := by
  have hs : count1047 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1047)) (countLit q [-94]) (countLit q [-96]) (count1047 q) 1 (meaningNeg94 q) (meaning1047 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1047 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1047 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1048 = true := by
  have hs : count1047 q = (countLit q [-94]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1048)) (countLit q [-94]) (countLit q [-96]) (count1047 q) 1 1 (meaningNeg94 q) (meaningNeg96 q) (meaning1048 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1048 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 1048 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1049 = true := by
  have hs : count1049 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1049)) (countLit q [-99]) (countLit q [-100]) (count1049 q) 1 (meaningNeg100 q) (meaning1049 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1049 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1049 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1049 = true := by
  have hs : count1049 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1049)) (countLit q [-99]) (countLit q [-100]) (count1049 q) 1 (meaningNeg99 q) (meaning1049 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1049 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1049 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1050 = true := by
  have hs : count1049 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1050)) (countLit q [-99]) (countLit q [-100]) (count1049 q) 1 1 (meaningNeg99 q) (meaningNeg100 q) (meaning1050 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 1050 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1051 = true := by
  have hs : count1051 q = (countLit q [-94, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-99, -100])
  have hm := merge_right (literal (valuationOf q) (1049)) (literal (valuationOf q) (1051)) (countLit q [-94, -96]) (countLit q [-99, -100]) (count1051 q) 1 (meaning1049 q) (meaning1051 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1051 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1052 = true := by
  have hs : count1051 q = (countLit q [-94, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-99, -100])
  have hm := merge_right (literal (valuationOf q) (1050)) (literal (valuationOf q) (1052)) (countLit q [-94, -96]) (countLit q [-99, -100]) (count1051 q) 2 (meaning1050 q) (meaning1052 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1052 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1051 = true := by
  have hs : count1051 q = (countLit q [-94, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-99, -100])
  have hm := merge_left (literal (valuationOf q) (1047)) (literal (valuationOf q) (1051)) (countLit q [-94, -96]) (countLit q [-99, -100]) (count1051 q) 1 (meaning1047 q) (meaning1051 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1051 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1052 = true := by
  have hs : count1051 q = (countLit q [-94, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-99, -100])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1049)) (literal (valuationOf q) (1052)) (countLit q [-94, -96]) (countLit q [-99, -100]) (count1051 q) 1 1 (meaning1047 q) (meaning1049 q) (meaning1052 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1049 = false ∨ valuation q 1052 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1053 = true := by
  have hs : count1051 q = (countLit q [-94, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-99, -100])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1050)) (literal (valuationOf q) (1053)) (countLit q [-94, -96]) (countLit q [-99, -100]) (count1051 q) 1 2 (meaning1047 q) (meaning1050 q) (meaning1053 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1050 = false ∨ valuation q 1053 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1052 = true := by
  have hs : count1051 q = (countLit q [-94, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-99, -100])
  have hm := merge_left (literal (valuationOf q) (1048)) (literal (valuationOf q) (1052)) (countLit q [-94, -96]) (countLit q [-99, -100]) (count1051 q) 2 (meaning1048 q) (meaning1052 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1052 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1053 = true := by
  have hs : count1051 q = (countLit q [-94, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-99, -100])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1049)) (literal (valuationOf q) (1053)) (countLit q [-94, -96]) (countLit q [-99, -100]) (count1051 q) 2 1 (meaning1048 q) (meaning1049 q) (meaning1053 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1049 = false ∨ valuation q 1053 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1054 = true := by
  have hs : count1051 q = (countLit q [-94, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -96]) (l₂ := [-99, -100])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1050)) (literal (valuationOf q) (1054)) (countLit q [-94, -96]) (countLit q [-99, -100]) (count1051 q) 2 2 (meaning1048 q) (meaning1050 q) (meaning1054 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1050 = false ∨ valuation q 1054 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1055 = true := by
  have hs : count1055 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1055)) (countLit q [-103]) (countLit q [-105]) (count1055 q) 1 (meaningNeg105 q) (meaning1055 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1055 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1055 = true := by
  have hs : count1055 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1055)) (countLit q [-103]) (countLit q [-105]) (count1055 q) 1 (meaningNeg103 q) (meaning1055 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1055 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1056 = true := by
  have hs : count1055 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1056)) (countLit q [-103]) (countLit q [-105]) (count1055 q) 1 1 (meaningNeg103 q) (meaningNeg105 q) (meaning1056 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 1056 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1057 = true := by
  have hs : count1057 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1057)) (countLit q [-107]) (countLit q [-108]) (count1057 q) 1 (meaningNeg108 q) (meaning1057 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1057 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1057 = true := by
  have hs : count1057 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1057)) (countLit q [-107]) (countLit q [-108]) (count1057 q) 1 (meaningNeg107 q) (meaning1057 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1057 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E153.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112153
