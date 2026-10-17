import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1084 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1049)) (literal (valuationOf q) (1073)) (literal (valuationOf q) (1084)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 3 3 (meaning1049 q) (meaning1073 q) (meaning1084 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1073 = false ∨ valuation q 1084 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1085 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1049)) (literal (valuationOf q) (1074)) (literal (valuationOf q) (1085)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 3 4 (meaning1049 q) (meaning1074 q) (meaning1085 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1074 = false ∨ valuation q 1085 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1075 = false ∨ valuationOf q 1086 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1049)) (literal (valuationOf q) (1075)) (literal (valuationOf q) (1086)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 3 5 (meaning1049 q) (meaning1075 q) (meaning1086 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1075 = false ∨ valuationOf q 1086 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1075 = false ∨ valuation q 1086 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1076 = false ∨ valuationOf q 1087 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1049)) (literal (valuationOf q) (1076)) (literal (valuationOf q) (1087)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 3 6 (meaning1049 q) (meaning1076 q) (meaning1087 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1076 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1076 = false ∨ valuation q 1087 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1077 = false ∨ valuationOf q 1088 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1049)) (literal (valuationOf q) (1077)) (literal (valuationOf q) (1088)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 3 7 (meaning1049 q) (meaning1077 q) (meaning1088 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1077 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1077 = false ∨ valuation q 1088 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1071 = false ∨ valuationOf q 1083 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1050)) (literal (valuationOf q) (1071)) (literal (valuationOf q) (1083)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 4 1 (meaning1050 q) (meaning1071 q) (meaning1083 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1071 = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1071 = false ∨ valuation q 1083 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1084 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1050)) (literal (valuationOf q) (1072)) (literal (valuationOf q) (1084)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 4 2 (meaning1050 q) (meaning1072 q) (meaning1084 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1072 = false ∨ valuation q 1084 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1085 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1050)) (literal (valuationOf q) (1073)) (literal (valuationOf q) (1085)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 4 3 (meaning1050 q) (meaning1073 q) (meaning1085 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1073 = false ∨ valuation q 1085 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1086 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1050)) (literal (valuationOf q) (1074)) (literal (valuationOf q) (1086)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 4 4 (meaning1050 q) (meaning1074 q) (meaning1086 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1086 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1074 = false ∨ valuation q 1086 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1075 = false ∨ valuationOf q 1087 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1050)) (literal (valuationOf q) (1075)) (literal (valuationOf q) (1087)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 4 5 (meaning1050 q) (meaning1075 q) (meaning1087 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1075 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1075 = false ∨ valuation q 1087 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1076 = false ∨ valuationOf q 1088 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1050)) (literal (valuationOf q) (1076)) (literal (valuationOf q) (1088)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 4 6 (meaning1050 q) (meaning1076 q) (meaning1088 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1076 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1076 = false ∨ valuation q 1088 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1077 = false ∨ valuationOf q 1089 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1050)) (literal (valuationOf q) (1077)) (literal (valuationOf q) (1089)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 4 7 (meaning1050 q) (meaning1077 q) (meaning1089 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1077 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1077 = false ∨ valuation q 1089 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1078 = false ∨ valuationOf q 1090 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1050)) (literal (valuationOf q) (1078)) (literal (valuationOf q) (1090)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 4 8 (meaning1050 q) (meaning1078 q) (meaning1090 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1078 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1078 = false ∨ valuation q 1090 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1071 = false ∨ valuationOf q 1084 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1051)) (literal (valuationOf q) (1071)) (literal (valuationOf q) (1084)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 5 1 (meaning1051 q) (meaning1071 q) (meaning1084 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1071 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1071 = false ∨ valuation q 1084 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1085 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1051)) (literal (valuationOf q) (1072)) (literal (valuationOf q) (1085)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 5 2 (meaning1051 q) (meaning1072 q) (meaning1085 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1072 = false ∨ valuation q 1085 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1086 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1051)) (literal (valuationOf q) (1073)) (literal (valuationOf q) (1086)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 5 3 (meaning1051 q) (meaning1073 q) (meaning1086 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1086 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1073 = false ∨ valuation q 1086 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1087 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1051)) (literal (valuationOf q) (1074)) (literal (valuationOf q) (1087)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 5 4 (meaning1051 q) (meaning1074 q) (meaning1087 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1074 = false ∨ valuation q 1087 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1075 = false ∨ valuationOf q 1088 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1051)) (literal (valuationOf q) (1075)) (literal (valuationOf q) (1088)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 5 5 (meaning1051 q) (meaning1075 q) (meaning1088 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1075 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1075 = false ∨ valuation q 1088 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1076 = false ∨ valuationOf q 1089 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1051)) (literal (valuationOf q) (1076)) (literal (valuationOf q) (1089)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 5 6 (meaning1051 q) (meaning1076 q) (meaning1089 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1076 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1076 = false ∨ valuation q 1089 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1077 = false ∨ valuationOf q 1090 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1051)) (literal (valuationOf q) (1077)) (literal (valuationOf q) (1090)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 5 7 (meaning1051 q) (meaning1077 q) (meaning1090 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1077 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1077 = false ∨ valuation q 1090 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1086 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1052)) (literal (valuationOf q) (1072)) (literal (valuationOf q) (1086)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 6 2 (meaning1052 q) (meaning1072 q) (meaning1086 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1086 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1072 = false ∨ valuation q 1086 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1087 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1052)) (literal (valuationOf q) (1073)) (literal (valuationOf q) (1087)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 6 3 (meaning1052 q) (meaning1073 q) (meaning1087 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1073 = false ∨ valuation q 1087 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1088 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1052)) (literal (valuationOf q) (1074)) (literal (valuationOf q) (1088)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 6 4 (meaning1052 q) (meaning1074 q) (meaning1088 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1074 = false ∨ valuation q 1088 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1052 = false ∨ valuationOf q 1076 = false ∨ valuationOf q 1090 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1052)) (literal (valuationOf q) (1076)) (literal (valuationOf q) (1090)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 6 6 (meaning1052 q) (meaning1076 q) (meaning1090 q) hs
  change valuationOf q 1052 = false ∨ valuationOf q 1076 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1052 = false ∨ valuation q 1076 = false ∨ valuation q 1090 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1087 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1053)) (literal (valuationOf q) (1072)) (literal (valuationOf q) (1087)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 7 2 (meaning1053 q) (meaning1072 q) (meaning1087 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1072 = false ∨ valuation q 1087 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1088 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1053)) (literal (valuationOf q) (1073)) (literal (valuationOf q) (1088)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 7 3 (meaning1053 q) (meaning1073 q) (meaning1088 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1073 = false ∨ valuation q 1088 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1102)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 1 7 (meaning1016 q) (meaning1085 q) (meaning1102 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1085 = false ∨ valuation q 1102 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1103)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 1 8 (meaning1016 q) (meaning1086 q) (meaning1103 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1086 = false ∨ valuation q 1103 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1104 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1104)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 1 9 (meaning1016 q) (meaning1087 q) (meaning1104 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1087 = false ∨ valuation q 1104 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1105 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1105)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 1 10 (meaning1016 q) (meaning1088 q) (meaning1105 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1088 = false ∨ valuation q 1105 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1106 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1106)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 1 11 (meaning1016 q) (meaning1089 q) (meaning1106 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1089 = false ∨ valuation q 1106 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) + (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (l₂ := [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1102)) (countLit q [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]) (count1095 q) 2 6 (meaning1017 q) (meaning1084 q) (meaning1102 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1084 = false ∨ valuation q 1102 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E097.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112097
