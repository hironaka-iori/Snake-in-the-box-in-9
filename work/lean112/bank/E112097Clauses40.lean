import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1043 = true := by
  have hs : count1043 q = (countLit q [-101, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -105]) (l₂ := [-106, -108])
  have hm := merge_left (literal (valuationOf q) (1039)) (literal (valuationOf q) (1043)) (countLit q [-101, -105]) (countLit q [-106, -108]) (count1043 q) 1 (meaning1039 q) (meaning1043 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1043 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1043 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1044 = true := by
  have hs : count1043 q = (countLit q [-101, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -105]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1041)) (literal (valuationOf q) (1044)) (countLit q [-101, -105]) (countLit q [-106, -108]) (count1043 q) 1 1 (meaning1039 q) (meaning1041 q) (meaning1044 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1044 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1041 = false ∨ valuation q 1044 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1042 = false ∨ valuationOf q 1045 = true := by
  have hs : count1043 q = (countLit q [-101, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -105]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1042)) (literal (valuationOf q) (1045)) (countLit q [-101, -105]) (countLit q [-106, -108]) (count1043 q) 1 2 (meaning1039 q) (meaning1042 q) (meaning1045 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1042 = false ∨ valuationOf q 1045 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1042 = false ∨ valuation q 1045 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1044 = true := by
  have hs : count1043 q = (countLit q [-101, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -105]) (l₂ := [-106, -108])
  have hm := merge_left (literal (valuationOf q) (1040)) (literal (valuationOf q) (1044)) (countLit q [-101, -105]) (countLit q [-106, -108]) (count1043 q) 2 (meaning1040 q) (meaning1044 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1044 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1044 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1045 = true := by
  have hs : count1043 q = (countLit q [-101, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -105]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1041)) (literal (valuationOf q) (1045)) (countLit q [-101, -105]) (countLit q [-106, -108]) (count1043 q) 2 1 (meaning1040 q) (meaning1041 q) (meaning1045 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1045 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1041 = false ∨ valuation q 1045 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1042 = false ∨ valuationOf q 1046 = true := by
  have hs : count1043 q = (countLit q [-101, -105]) + (countLit q [-106, -108]) := List.countP_append (p := literal q) (l₁ := [-101, -105]) (l₂ := [-106, -108])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1042)) (literal (valuationOf q) (1046)) (countLit q [-101, -105]) (countLit q [-106, -108]) (count1043 q) 2 2 (meaning1040 q) (meaning1042 q) (meaning1046 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1042 = false ∨ valuationOf q 1046 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1042 = false ∨ valuation q 1046 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1043 = false ∨ valuationOf q 1047 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_right (literal (valuationOf q) (1043)) (literal (valuationOf q) (1047)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 1 (meaning1043 q) (meaning1047 q) hs
  change valuationOf q 1043 = false ∨ valuationOf q 1047 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1043 = false ∨ valuation q 1047 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1044 = false ∨ valuationOf q 1048 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_right (literal (valuationOf q) (1044)) (literal (valuationOf q) (1048)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 2 (meaning1044 q) (meaning1048 q) hs
  change valuationOf q 1044 = false ∨ valuationOf q 1048 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1044 = false ∨ valuation q 1048 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1045 = false ∨ valuationOf q 1049 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_right (literal (valuationOf q) (1045)) (literal (valuationOf q) (1049)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 3 (meaning1045 q) (meaning1049 q) hs
  change valuationOf q 1045 = false ∨ valuationOf q 1049 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1045 = false ∨ valuation q 1049 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1046 = false ∨ valuationOf q 1050 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_right (literal (valuationOf q) (1046)) (literal (valuationOf q) (1050)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 4 (meaning1046 q) (meaning1050 q) hs
  change valuationOf q 1046 = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1046 = false ∨ valuation q 1050 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1047 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_left (literal (valuationOf q) (1035)) (literal (valuationOf q) (1047)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 1 (meaning1035 q) (meaning1047 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1047 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1047 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1043 = false ∨ valuationOf q 1048 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1043)) (literal (valuationOf q) (1048)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 1 1 (meaning1035 q) (meaning1043 q) (meaning1048 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1043 = false ∨ valuationOf q 1048 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1043 = false ∨ valuation q 1048 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1044 = false ∨ valuationOf q 1049 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1044)) (literal (valuationOf q) (1049)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 1 2 (meaning1035 q) (meaning1044 q) (meaning1049 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1044 = false ∨ valuationOf q 1049 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1044 = false ∨ valuation q 1049 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1045 = false ∨ valuationOf q 1050 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1045)) (literal (valuationOf q) (1050)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 1 3 (meaning1035 q) (meaning1045 q) (meaning1050 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1045 = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1045 = false ∨ valuation q 1050 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1035 = false ∨ valuationOf q 1046 = false ∨ valuationOf q 1051 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_two (literal (valuationOf q) (1035)) (literal (valuationOf q) (1046)) (literal (valuationOf q) (1051)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 1 4 (meaning1035 q) (meaning1046 q) (meaning1051 q) hs
  change valuationOf q 1035 = false ∨ valuationOf q 1046 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1035 = false ∨ valuation q 1046 = false ∨ valuation q 1051 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1048 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_left (literal (valuationOf q) (1036)) (literal (valuationOf q) (1048)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 2 (meaning1036 q) (meaning1048 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1048 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1048 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1043 = false ∨ valuationOf q 1049 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1043)) (literal (valuationOf q) (1049)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 2 1 (meaning1036 q) (meaning1043 q) (meaning1049 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1043 = false ∨ valuationOf q 1049 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1043 = false ∨ valuation q 1049 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1044 = false ∨ valuationOf q 1050 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1044)) (literal (valuationOf q) (1050)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 2 2 (meaning1036 q) (meaning1044 q) (meaning1050 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1044 = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1044 = false ∨ valuation q 1050 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1045 = false ∨ valuationOf q 1051 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1045)) (literal (valuationOf q) (1051)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 2 3 (meaning1036 q) (meaning1045 q) (meaning1051 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1045 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1045 = false ∨ valuation q 1051 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1036 = false ∨ valuationOf q 1046 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_two (literal (valuationOf q) (1036)) (literal (valuationOf q) (1046)) (literal (valuationOf q) (1052)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 2 4 (meaning1036 q) (meaning1046 q) (meaning1052 q) hs
  change valuationOf q 1036 = false ∨ valuationOf q 1046 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1036 = false ∨ valuation q 1046 = false ∨ valuation q 1052 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1049 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_left (literal (valuationOf q) (1037)) (literal (valuationOf q) (1049)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 3 (meaning1037 q) (meaning1049 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1049 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1049 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1043 = false ∨ valuationOf q 1050 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1043)) (literal (valuationOf q) (1050)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 3 1 (meaning1037 q) (meaning1043 q) (meaning1050 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1043 = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1043 = false ∨ valuation q 1050 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1044 = false ∨ valuationOf q 1051 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1044)) (literal (valuationOf q) (1051)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 3 2 (meaning1037 q) (meaning1044 q) (meaning1051 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1044 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1044 = false ∨ valuation q 1051 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1045 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1045)) (literal (valuationOf q) (1052)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 3 3 (meaning1037 q) (meaning1045 q) (meaning1052 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1045 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1045 = false ∨ valuation q 1052 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1037 = false ∨ valuationOf q 1046 = false ∨ valuationOf q 1053 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_two (literal (valuationOf q) (1037)) (literal (valuationOf q) (1046)) (literal (valuationOf q) (1053)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 3 4 (meaning1037 q) (meaning1046 q) (meaning1053 q) hs
  change valuationOf q 1037 = false ∨ valuationOf q 1046 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1037 = false ∨ valuation q 1046 = false ∨ valuation q 1053 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1038 = false ∨ valuationOf q 1044 = false ∨ valuationOf q 1052 = true := by
  have hs : count1047 q = (countLit q [-94, -95, -97, -100]) + (countLit q [-101, -105, -106, -108]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100]) (l₂ := [-101, -105, -106, -108])
  have hm := merge_two (literal (valuationOf q) (1038)) (literal (valuationOf q) (1044)) (literal (valuationOf q) (1052)) (countLit q [-94, -95, -97, -100]) (countLit q [-101, -105, -106, -108]) (count1047 q) 4 2 (meaning1038 q) (meaning1044 q) (meaning1052 q) hs
  change valuationOf q 1038 = false ∨ valuationOf q 1044 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1038 = false ∨ valuation q 1044 = false ∨ valuation q 1052 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1055 = true := by
  have hs : count1055 q = (countLit q [-109]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-111])
  have hm := merge_right (literal (valuationOf q) (-111)) (literal (valuationOf q) (1055)) (countLit q [-109]) (countLit q [-111]) (count1055 q) 1 (meaningNeg111 q) (meaning1055 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1055 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1055 = true := by
  have hs : count1055 q = (countLit q [-109]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-111])
  have hm := merge_left (literal (valuationOf q) (-109)) (literal (valuationOf q) (1055)) (countLit q [-109]) (countLit q [-111]) (count1055 q) 1 (meaningNeg109 q) (meaning1055 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1055 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 111 = true ∨ valuationOf q 1056 = true := by
  have hs : count1055 q = (countLit q [-109]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-111])
  have hm := merge_two (literal (valuationOf q) (-109)) (literal (valuationOf q) (-111)) (literal (valuationOf q) (1056)) (countLit q [-109]) (countLit q [-111]) (count1055 q) 1 1 (meaningNeg109 q) (meaningNeg111 q) (meaning1056 q) hs
  change (! (valuationOf q 109)) = false ∨ (! (valuationOf q 111)) = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 1056 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1057 = true := by
  have hs : count1057 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_right (literal (valuationOf q) (-114)) (literal (valuationOf q) (1057)) (countLit q [-113]) (countLit q [-114]) (count1057 q) 1 (meaningNeg114 q) (meaning1057 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1057 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1057 = true := by
  have hs : count1057 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_left (literal (valuationOf q) (-113)) (literal (valuationOf q) (1057)) (countLit q [-113]) (countLit q [-114]) (count1057 q) 1 (meaningNeg113 q) (meaning1057 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1057 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 114 = true ∨ valuationOf q 1058 = true := by
  have hs : count1057 q = (countLit q [-113]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-114])
  have hm := merge_two (literal (valuationOf q) (-113)) (literal (valuationOf q) (-114)) (literal (valuationOf q) (1058)) (countLit q [-113]) (countLit q [-114]) (count1057 q) 1 1 (meaningNeg113 q) (meaningNeg114 q) (meaning1058 q) hs
  change (! (valuationOf q 113)) = false ∨ (! (valuationOf q 114)) = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 114 = true ∨ valuation q 1058 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E097.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112097
