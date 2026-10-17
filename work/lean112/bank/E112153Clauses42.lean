import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1103 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_right (literal (valuationOf q) (1103)) (literal (valuationOf q) (1119)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 9 (meaning1103 q) (meaning1119 q) hs
  change valuationOf q 1103 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1103 = false ∨ valuation q 1119 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1104 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_right (literal (valuationOf q) (1104)) (literal (valuationOf q) (1120)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 10 (meaning1104 q) (meaning1120 q) hs
  change valuationOf q 1104 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1104 = false ∨ valuation q 1120 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1105 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_right (literal (valuationOf q) (1105)) (literal (valuationOf q) (1121)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 11 (meaning1105 q) (meaning1121 q) hs
  change valuationOf q 1105 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1105 = false ∨ valuation q 1121 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1119)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 1 8 (meaning1032 q) (meaning1102 q) (meaning1119 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1102 = false ∨ valuation q 1119 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1103)) (literal (valuationOf q) (1120)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 1 9 (meaning1032 q) (meaning1103 q) (meaning1120 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1103 = false ∨ valuation q 1120 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1104)) (literal (valuationOf q) (1121)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 1 10 (meaning1032 q) (meaning1104 q) (meaning1121 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1104 = false ∨ valuation q 1121 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1105)) (literal (valuationOf q) (1122)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 1 11 (meaning1032 q) (meaning1105 q) (meaning1122 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1105 = false ∨ valuation q 1122 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1032 = false ∨ valuationOf q 1106 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1032)) (literal (valuationOf q) (1106)) (literal (valuationOf q) (1123)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 1 12 (meaning1032 q) (meaning1106 q) (meaning1123 q) hs
  change valuationOf q 1032 = false ∨ valuationOf q 1106 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1032 = false ∨ valuation q 1106 = false ∨ valuation q 1123 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1119)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 2 7 (meaning1033 q) (meaning1101 q) (meaning1119 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1101 = false ∨ valuation q 1119 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1120)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 2 8 (meaning1033 q) (meaning1102 q) (meaning1120 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1102 = false ∨ valuation q 1120 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1103)) (literal (valuationOf q) (1121)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 2 9 (meaning1033 q) (meaning1103 q) (meaning1121 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1103 = false ∨ valuation q 1121 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1104)) (literal (valuationOf q) (1122)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 2 10 (meaning1033 q) (meaning1104 q) (meaning1122 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1104 = false ∨ valuation q 1122 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1105)) (literal (valuationOf q) (1123)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 2 11 (meaning1033 q) (meaning1105 q) (meaning1123 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1105 = false ∨ valuation q 1123 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1033 = false ∨ valuationOf q 1106 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1033)) (literal (valuationOf q) (1106)) (literal (valuationOf q) (1124)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 2 12 (meaning1033 q) (meaning1106 q) (meaning1124 q) hs
  change valuationOf q 1033 = false ∨ valuationOf q 1106 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1033 = false ∨ valuation q 1106 = false ∨ valuation q 1124 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1119)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 3 6 (meaning1034 q) (meaning1100 q) (meaning1119 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1100 = false ∨ valuation q 1119 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1120)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 3 7 (meaning1034 q) (meaning1101 q) (meaning1120 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1101 = false ∨ valuation q 1120 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1121)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 3 8 (meaning1034 q) (meaning1102 q) (meaning1121 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1102 = false ∨ valuation q 1121 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1103)) (literal (valuationOf q) (1122)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 3 9 (meaning1034 q) (meaning1103 q) (meaning1122 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1103 = false ∨ valuation q 1122 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1104)) (literal (valuationOf q) (1123)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 3 10 (meaning1034 q) (meaning1104 q) (meaning1123 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1104 = false ∨ valuation q 1123 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1105)) (literal (valuationOf q) (1124)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 3 11 (meaning1034 q) (meaning1105 q) (meaning1124 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1105 = false ∨ valuation q 1124 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1034 = false ∨ valuationOf q 1106 = false ∨ valuationOf q 1125 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1034)) (literal (valuationOf q) (1106)) (literal (valuationOf q) (1125)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 3 12 (meaning1034 q) (meaning1106 q) (meaning1125 q) hs
  change valuationOf q 1034 = false ∨ valuationOf q 1106 = false ∨ valuationOf q 1125 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1034 = false ∨ valuation q 1106 = false ∨ valuation q 1125 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1119)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 4 5 (meaning1035 q) (meaning1099 q) (meaning1119 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1099 = false ∨ valuation q 1119 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1120)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 4 6 (meaning1035 q) (meaning1100 q) (meaning1120 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1100 = false ∨ valuation q 1120 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1101)) (literal (valuationOf q) (1121)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 4 7 (meaning1035 q) (meaning1101 q) (meaning1121 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1101 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1101 = false ∨ valuation q 1121 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1122 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1102)) (literal (valuationOf q) (1122)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 4 8 (meaning1035 q) (meaning1102 q) (meaning1122 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1102 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1102 = false ∨ valuation q 1122 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1123 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1103)) (literal (valuationOf q) (1123)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 4 9 (meaning1035 q) (meaning1103 q) (meaning1123 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1103 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1103 = false ∨ valuation q 1123 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1124 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1104)) (literal (valuationOf q) (1124)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 4 10 (meaning1035 q) (meaning1104 q) (meaning1124 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1104 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1104 = false ∨ valuation q 1124 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1125 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1105)) (literal (valuationOf q) (1125)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 4 11 (meaning1035 q) (meaning1105 q) (meaning1125 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1125 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1105 = false ∨ valuation q 1125 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1106 = false ∨ valuationOf q 1126 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1106)) (literal (valuationOf q) (1126)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 4 12 (meaning1035 q) (meaning1106 q) (meaning1126 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1106 = false ∨ valuationOf q 1126 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1106 = false ∨ valuation q 1126 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1119 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1098)) (literal (valuationOf q) (1119)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 5 4 (meaning1036 q) (meaning1098 q) (meaning1119 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1098 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1098 = false ∨ valuation q 1119 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1120 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1099)) (literal (valuationOf q) (1120)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 5 5 (meaning1036 q) (meaning1099 q) (meaning1120 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1099 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1099 = false ∨ valuation q 1120 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1121 = true := by
  have hs : count1111 q = (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) + (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (l₂ := [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1100)) (literal (valuationOf q) (1121)) (countLit q [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]) (count1111 q) 5 6 (meaning1036 q) (meaning1100 q) (meaning1121 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1100 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1100 = false ∨ valuation q 1121 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E153.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112153
