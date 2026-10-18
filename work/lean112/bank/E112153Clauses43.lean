import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1122)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 5 7 (meaning1036 q) (meaning1101 q) (meaning1122 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1101 = false ∨ valuation q 1122 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1123)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 5 8 (meaning1036 q) (meaning1102 q) (meaning1123 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1102 = false ∨ valuation q 1123 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1103)) (literal (valuationOf q) (1124)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 5 9 (meaning1036 q) (meaning1103 q) (meaning1124 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1103 = false ∨ valuation q 1124 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1125 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1104)) (literal (valuationOf q) (1125)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 5 10 (meaning1036 q) (meaning1104 q) (meaning1125 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1125 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1104 = false ∨ valuation q 1125 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1126 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1105)) (literal (valuationOf q) (1126)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 5 11 (meaning1036 q) (meaning1105 q) (meaning1126 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1126 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1105 = false ∨ valuation q 1126 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1120)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 6 4 (meaning1037 q) (meaning1098 q) (meaning1120 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1098 = false ∨ valuation q 1120 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1121)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 6 5 (meaning1037 q) (meaning1099 q) (meaning1121 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1099 = false ∨ valuation q 1121 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1122)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 6 6 (meaning1037 q) (meaning1100 q) (meaning1122 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1100 = false ∨ valuation q 1122 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1123)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 6 7 (meaning1037 q) (meaning1101 q) (meaning1123 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1101 = false ∨ valuation q 1123 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1124)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 6 8 (meaning1037 q) (meaning1102 q) (meaning1124 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1102 = false ∨ valuation q 1124 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1125 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1103)) (literal (valuationOf q) (1125)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 6 9 (meaning1037 q) (meaning1103 q) (meaning1125 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1125 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1103 = false ∨ valuation q 1125 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1126 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1104)) (literal (valuationOf q) (1126)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 6 10 (meaning1037 q) (meaning1104 q) (meaning1126 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1126 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1104 = false ∨ valuation q 1126 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1121)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 7 4 (meaning1038 q) (meaning1098 q) (meaning1121 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1098 = false ∨ valuation q 1121 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1122)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 7 5 (meaning1038 q) (meaning1099 q) (meaning1122 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1099 = false ∨ valuation q 1122 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1123)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 7 6 (meaning1038 q) (meaning1100 q) (meaning1123 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1100 = false ∨ valuation q 1123 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1124)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 7 7 (meaning1038 q) (meaning1101 q) (meaning1124 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1101 = false ∨ valuation q 1124 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1125 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1125)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 7 8 (meaning1038 q) (meaning1102 q) (meaning1125 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1125 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1102 = false ∨ valuation q 1125 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1126 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1103)) (literal (valuationOf q) (1126)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 7 9 (meaning1038 q) (meaning1103 q) (meaning1126 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1126 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1103 = false ∨ valuation q 1126 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1121)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 8 3 (meaning1039 q) (meaning1097 q) (meaning1121 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1097 = false ∨ valuation q 1121 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1122)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 8 4 (meaning1039 q) (meaning1098 q) (meaning1122 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1098 = false ∨ valuation q 1122 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1123)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 8 5 (meaning1039 q) (meaning1099 q) (meaning1123 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1099 = false ∨ valuation q 1123 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1124)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 8 6 (meaning1039 q) (meaning1100 q) (meaning1124 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1100 = false ∨ valuation q 1124 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1125 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1125)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 8 7 (meaning1039 q) (meaning1101 q) (meaning1125 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1125 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1101 = false ∨ valuation q 1125 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1126 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1126)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 8 8 (meaning1039 q) (meaning1102 q) (meaning1126 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1126 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1102 = false ∨ valuation q 1126 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1097)) (literal (valuationOf q) (1122)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 9 3 (meaning1040 q) (meaning1097 q) (meaning1122 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1097 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1097 = false ∨ valuation q 1122 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1123)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 9 4 (meaning1040 q) (meaning1098 q) (meaning1123 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1098 = false ∨ valuation q 1123 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1124)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 9 5 (meaning1040 q) (meaning1099 q) (meaning1124 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1099 = false ∨ valuation q 1124 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 971 = false ∨ valuationOf q 1126 = false ∨ valuationOf q 1154 = true := by
  have hs : count1133 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) + (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (l₂ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (971)) (literal (valuationOf q) (1126)) (literal (valuationOf q) (1154)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1133 q) 6 16 (meaning971 q) (meaning1126 q) (meaning1154 q) hs
  change valuationOf q 971 = false ∨ valuationOf q 1126 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 971 = false ∨ valuation q 1126 = false ∨ valuation q 1154 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 972 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1154 = true := by
  have hs : count1133 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) + (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (l₂ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (972)) (literal (valuationOf q) (1125)) (literal (valuationOf q) (1154)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1133 q) 7 15 (meaning972 q) (meaning1125 q) (meaning1154 q) hs
  change valuationOf q 972 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 972 = false ∨ valuation q 1125 = false ∨ valuation q 1154 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1154 = true := by
  have hs : count1133 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) + (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (l₂ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (973)) (literal (valuationOf q) (1124)) (literal (valuationOf q) (1154)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1133 q) 8 14 (meaning973 q) (meaning1124 q) (meaning1154 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 1124 = false ∨ valuation q 1154 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1154 = true := by
  have hs : count1133 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) + (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (l₂ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (974)) (literal (valuationOf q) (1123)) (literal (valuationOf q) (1154)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1133 q) 9 13 (meaning974 q) (meaning1123 q) (meaning1154 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 1123 = false ∨ valuation q 1154 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 975 = false ∨ valuationOf q 1122 = false ∨ valuationOf q 1154 = true := by
  have hs : count1133 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) + (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (l₂ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (975)) (literal (valuationOf q) (1122)) (literal (valuationOf q) (1154)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1133 q) 10 12 (meaning975 q) (meaning1122 q) (meaning1154 q) hs
  change valuationOf q 975 = false ∨ valuationOf q 1122 = false ∨ valuationOf q 1154 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 975 = false ∨ valuation q 1122 = false ∨ valuation q 1154 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E153.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112153
