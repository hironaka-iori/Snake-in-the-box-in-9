import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1088 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1088)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 1 1 (meaning1075 q) (meaning1083 q) (meaning1088 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1083 = false ∨ valuation q 1088 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1089 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1089)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 1 2 (meaning1075 q) (meaning1084 q) (meaning1089 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1084 = false ∨ valuation q 1089 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1090 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1090)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 1 3 (meaning1075 q) (meaning1085 q) (meaning1090 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1085 = false ∨ valuation q 1090 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1091 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1075)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1091)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 1 4 (meaning1075 q) (meaning1086 q) (meaning1091 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1086 = false ∨ valuation q 1091 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1089 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1089)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 2 1 (meaning1076 q) (meaning1083 q) (meaning1089 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1089 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1083 = false ∨ valuation q 1089 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1090 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1090)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 2 2 (meaning1076 q) (meaning1084 q) (meaning1090 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1084 = false ∨ valuation q 1090 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1091 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1091)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 2 3 (meaning1076 q) (meaning1085 q) (meaning1091 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1085 = false ∨ valuation q 1091 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1092 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1076)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1092)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 2 4 (meaning1076 q) (meaning1086 q) (meaning1092 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1092 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1086 = false ∨ valuation q 1092 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1090 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1077)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1090)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 3 1 (meaning1077 q) (meaning1083 q) (meaning1090 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1083 = false ∨ valuation q 1090 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1091 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1077)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1091)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 3 2 (meaning1077 q) (meaning1084 q) (meaning1091 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1084 = false ∨ valuation q 1091 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1092 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1077)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1092)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 3 3 (meaning1077 q) (meaning1085 q) (meaning1092 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1092 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1085 = false ∨ valuation q 1092 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1093 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1077)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1093)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 3 4 (meaning1077 q) (meaning1086 q) (meaning1093 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1093 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1086 = false ∨ valuation q 1093 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1078 = false ∨ valuationOf q 1090 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_left (literal (valuationOf q) (1078)) (literal (valuationOf q) (1090)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 4 (meaning1078 q) (meaning1090 q) hs
  change valuationOf q 1078 = false ∨ valuationOf q 1090 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1078 = false ∨ valuation q 1090 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1078 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1091 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1078)) (literal (valuationOf q) (1083)) (literal (valuationOf q) (1091)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 4 1 (meaning1078 q) (meaning1083 q) (meaning1091 q) hs
  change valuationOf q 1078 = false ∨ valuationOf q 1083 = false ∨ valuationOf q 1091 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1078 = false ∨ valuation q 1083 = false ∨ valuation q 1091 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1078 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1092 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1078)) (literal (valuationOf q) (1084)) (literal (valuationOf q) (1092)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 4 2 (meaning1078 q) (meaning1084 q) (meaning1092 q) hs
  change valuationOf q 1078 = false ∨ valuationOf q 1084 = false ∨ valuationOf q 1092 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1078 = false ∨ valuation q 1084 = false ∨ valuation q 1092 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1078 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1093 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1078)) (literal (valuationOf q) (1085)) (literal (valuationOf q) (1093)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 4 3 (meaning1078 q) (meaning1085 q) (meaning1093 q) hs
  change valuationOf q 1078 = false ∨ valuationOf q 1085 = false ∨ valuationOf q 1093 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1078 = false ∨ valuation q 1085 = false ∨ valuation q 1093 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1078 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1094 = true := by
  have hs : count1087 q = (countLit q [-111, -112, -113, -115]) + (countLit q [-117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -112, -113, -115]) (l₂ := [-117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1078)) (literal (valuationOf q) (1086)) (literal (valuationOf q) (1094)) (countLit q [-111, -112, -113, -115]) (countLit q [-117, -118, -121, -123]) (count1087 q) 4 4 (meaning1078 q) (meaning1086 q) (meaning1094 q) hs
  change valuationOf q 1078 = false ∨ valuationOf q 1086 = false ∨ valuationOf q 1094 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1078 = false ∨ valuation q 1086 = false ∨ valuation q 1094 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1090 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_right (literal (valuationOf q) (1090)) (literal (valuationOf q) (1098)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 4 (meaning1090 q) (meaning1098 q) hs
  change valuationOf q 1090 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1090 = false ∨ valuation q 1098 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1091 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_right (literal (valuationOf q) (1091)) (literal (valuationOf q) (1099)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 5 (meaning1091 q) (meaning1099 q) hs
  change valuationOf q 1091 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1091 = false ∨ valuation q 1099 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1092 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_right (literal (valuationOf q) (1092)) (literal (valuationOf q) (1100)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 6 (meaning1092 q) (meaning1100 q) hs
  change valuationOf q 1092 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1092 = false ∨ valuation q 1100 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1093 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_right (literal (valuationOf q) (1093)) (literal (valuationOf q) (1101)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 7 (meaning1093 q) (meaning1101 q) hs
  change valuationOf q 1093 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1093 = false ∨ valuation q 1101 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1097 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1097)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 1 2 (meaning1063 q) (meaning1088 q) (meaning1097 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1097 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1088 = false ∨ valuation q 1097 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1098)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 1 3 (meaning1063 q) (meaning1089 q) (meaning1098 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1089 = false ∨ valuation q 1098 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1099)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 1 4 (meaning1063 q) (meaning1090 q) (meaning1099 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1090 = false ∨ valuation q 1099 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1100)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 1 5 (meaning1063 q) (meaning1091 q) (meaning1100 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1091 = false ∨ valuation q 1100 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1101)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 1 6 (meaning1063 q) (meaning1092 q) (meaning1101 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1092 = false ∨ valuation q 1101 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1093)) (literal (valuationOf q) (1102)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 1 7 (meaning1063 q) (meaning1093 q) (meaning1102 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1093 = false ∨ valuation q 1102 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1094)) (literal (valuationOf q) (1103)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 1 8 (meaning1063 q) (meaning1094 q) (meaning1103 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1094 = false ∨ valuation q 1103 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1098 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1098)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 2 2 (meaning1064 q) (meaning1088 q) (meaning1098 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1098 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1088 = false ∨ valuation q 1098 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1099)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 2 3 (meaning1064 q) (meaning1089 q) (meaning1099 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1089 = false ∨ valuation q 1099 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1100)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 2 4 (meaning1064 q) (meaning1090 q) (meaning1100 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1090 = false ∨ valuation q 1100 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1101)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 2 5 (meaning1064 q) (meaning1091 q) (meaning1101 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1091 = false ∨ valuation q 1101 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E153.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112153
