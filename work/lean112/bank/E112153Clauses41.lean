import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1102)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 2 6 (meaning1064 q) (meaning1092 q) (meaning1102 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1092 = false ∨ valuation q 1102 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1093)) (literal (valuationOf q) (1103)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 2 7 (meaning1064 q) (meaning1093 q) (meaning1103 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1093 = false ∨ valuation q 1103 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1099)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 3 2 (meaning1065 q) (meaning1088 q) (meaning1099 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1088 = false ∨ valuation q 1099 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1100)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 3 3 (meaning1065 q) (meaning1089 q) (meaning1100 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1089 = false ∨ valuation q 1100 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1101)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 3 4 (meaning1065 q) (meaning1090 q) (meaning1101 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1090 = false ∨ valuation q 1101 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1102)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 3 5 (meaning1065 q) (meaning1091 q) (meaning1102 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1091 = false ∨ valuation q 1102 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1103)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 3 6 (meaning1065 q) (meaning1092 q) (meaning1103 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1092 = false ∨ valuation q 1103 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1104 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1093)) (literal (valuationOf q) (1104)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 3 7 (meaning1065 q) (meaning1093 q) (meaning1104 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1093 = false ∨ valuation q 1104 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1105 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1065)) (literal (valuationOf q) (1094)) (literal (valuationOf q) (1105)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 3 8 (meaning1065 q) (meaning1094 q) (meaning1105 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1094 = false ∨ valuation q 1105 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1087)) (literal (valuationOf q) (1099)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 4 1 (meaning1066 q) (meaning1087 q) (meaning1099 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1087 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1087 = false ∨ valuation q 1099 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1100)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 4 2 (meaning1066 q) (meaning1088 q) (meaning1100 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1088 = false ∨ valuation q 1100 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1101)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 4 3 (meaning1066 q) (meaning1089 q) (meaning1101 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1089 = false ∨ valuation q 1101 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1102)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 4 4 (meaning1066 q) (meaning1090 q) (meaning1102 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1090 = false ∨ valuation q 1102 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1103)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 4 5 (meaning1066 q) (meaning1091 q) (meaning1103 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1091 = false ∨ valuation q 1103 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1104 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1104)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 4 6 (meaning1066 q) (meaning1092 q) (meaning1104 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1092 = false ∨ valuation q 1104 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1105 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1093)) (literal (valuationOf q) (1105)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 4 7 (meaning1066 q) (meaning1093 q) (meaning1105 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1093 = false ∨ valuation q 1105 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1106 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1066)) (literal (valuationOf q) (1094)) (literal (valuationOf q) (1106)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 4 8 (meaning1066 q) (meaning1094 q) (meaning1106 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1094 = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1094 = false ∨ valuation q 1106 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1101 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1101)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 5 2 (meaning1067 q) (meaning1088 q) (meaning1101 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1101 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1088 = false ∨ valuation q 1101 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1102)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 5 3 (meaning1067 q) (meaning1089 q) (meaning1102 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1089 = false ∨ valuation q 1102 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1103)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 5 4 (meaning1067 q) (meaning1090 q) (meaning1103 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1090 = false ∨ valuation q 1103 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1104 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1104)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 5 5 (meaning1067 q) (meaning1091 q) (meaning1104 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1091 = false ∨ valuation q 1104 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1105 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1105)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 5 6 (meaning1067 q) (meaning1092 q) (meaning1105 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1092 = false ∨ valuation q 1105 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1106 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1067)) (literal (valuationOf q) (1093)) (literal (valuationOf q) (1106)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 5 7 (meaning1067 q) (meaning1093 q) (meaning1106 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1093 = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1093 = false ∨ valuation q 1106 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1102 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1102)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 6 2 (meaning1068 q) (meaning1088 q) (meaning1102 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1102 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1088 = false ∨ valuation q 1102 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1103)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 6 3 (meaning1068 q) (meaning1089 q) (meaning1103 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1089 = false ∨ valuation q 1103 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1104 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1104)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 6 4 (meaning1068 q) (meaning1090 q) (meaning1104 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1090 = false ∨ valuation q 1104 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1105 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1105)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 6 5 (meaning1068 q) (meaning1091 q) (meaning1105 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1091 = false ∨ valuation q 1105 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1106 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1068)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1106)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 6 6 (meaning1068 q) (meaning1092 q) (meaning1106 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1092 = false ∨ valuation q 1106 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1069 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1103 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1069)) (literal (valuationOf q) (1088)) (literal (valuationOf q) (1103)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 7 2 (meaning1069 q) (meaning1088 q) (meaning1103 q) hs
  change valuationOf q 1069 = false ∨ valuationOf q 1088 = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1069 = false ∨ valuation q 1088 = false ∨ valuation q 1103 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1069 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1104 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1069)) (literal (valuationOf q) (1089)) (literal (valuationOf q) (1104)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 7 3 (meaning1069 q) (meaning1089 q) (meaning1104 q) hs
  change valuationOf q 1069 = false ∨ valuationOf q 1089 = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1069 = false ∨ valuation q 1089 = false ∨ valuation q 1104 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1069 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1105 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1069)) (literal (valuationOf q) (1090)) (literal (valuationOf q) (1105)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 7 4 (meaning1069 q) (meaning1090 q) (meaning1105 q) hs
  change valuationOf q 1069 = false ∨ valuationOf q 1090 = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1069 = false ∨ valuation q 1090 = false ∨ valuation q 1105 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1069 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1106 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) + (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -99, -100, -103, -105, -107, -108]) (l₂ := [-111, -112, -113, -115, -117, -118, -121, -123])
  have hm := merge_two (literal (valuationOf q) (1069)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1106)) (countLit q [-94, -96, -99, -100, -103, -105, -107, -108]) (countLit q [-111, -112, -113, -115, -117, -118, -121, -123]) (count1095 q) 7 5 (meaning1069 q) (meaning1091 q) (meaning1106 q) hs
  change valuationOf q 1069 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1069 = false ∨ valuation q 1091 = false ∨ valuation q 1106 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E153.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112153
