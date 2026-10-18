import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1057 = false ∨ valuationOf q 1059 = true := by
  have hs : count1059 q = (countLit q [-109, -111]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -111]) (l₂ := [-113, -114])
  have hm := merge_right (literal (valuationOf q) (1057)) (literal (valuationOf q) (1059)) (countLit q [-109, -111]) (countLit q [-113, -114]) (count1059 q) 1 (meaning1057 q) (meaning1059 q) hs
  change valuationOf q 1057 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1057 = false ∨ valuation q 1059 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1058 = false ∨ valuationOf q 1060 = true := by
  have hs : count1059 q = (countLit q [-109, -111]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -111]) (l₂ := [-113, -114])
  have hm := merge_right (literal (valuationOf q) (1058)) (literal (valuationOf q) (1060)) (countLit q [-109, -111]) (countLit q [-113, -114]) (count1059 q) 2 (meaning1058 q) (meaning1060 q) hs
  change valuationOf q 1058 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1058 = false ∨ valuation q 1060 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1055 = false ∨ valuationOf q 1059 = true := by
  have hs : count1059 q = (countLit q [-109, -111]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -111]) (l₂ := [-113, -114])
  have hm := merge_left (literal (valuationOf q) (1055)) (literal (valuationOf q) (1059)) (countLit q [-109, -111]) (countLit q [-113, -114]) (count1059 q) 1 (meaning1055 q) (meaning1059 q) hs
  change valuationOf q 1055 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1055 = false ∨ valuation q 1059 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1055 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1060 = true := by
  have hs : count1059 q = (countLit q [-109, -111]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -111]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (1055)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1060)) (countLit q [-109, -111]) (countLit q [-113, -114]) (count1059 q) 1 1 (meaning1055 q) (meaning1057 q) (meaning1060 q) hs
  change valuationOf q 1055 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1055 = false ∨ valuation q 1057 = false ∨ valuation q 1060 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1055 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1061 = true := by
  have hs : count1059 q = (countLit q [-109, -111]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -111]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (1055)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1061)) (countLit q [-109, -111]) (countLit q [-113, -114]) (count1059 q) 1 2 (meaning1055 q) (meaning1058 q) (meaning1061 q) hs
  change valuationOf q 1055 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1061 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1055 = false ∨ valuation q 1058 = false ∨ valuation q 1061 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1056 = false ∨ valuationOf q 1060 = true := by
  have hs : count1059 q = (countLit q [-109, -111]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -111]) (l₂ := [-113, -114])
  have hm := merge_left (literal (valuationOf q) (1056)) (literal (valuationOf q) (1060)) (countLit q [-109, -111]) (countLit q [-113, -114]) (count1059 q) 2 (meaning1056 q) (meaning1060 q) hs
  change valuationOf q 1056 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1056 = false ∨ valuation q 1060 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1056 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1061 = true := by
  have hs : count1059 q = (countLit q [-109, -111]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -111]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (1056)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1061)) (countLit q [-109, -111]) (countLit q [-113, -114]) (count1059 q) 2 1 (meaning1056 q) (meaning1057 q) (meaning1061 q) hs
  change valuationOf q 1056 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1061 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1056 = false ∨ valuation q 1057 = false ∨ valuation q 1061 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1056 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1062 = true := by
  have hs : count1059 q = (countLit q [-109, -111]) + (countLit q [-113, -114]) := List.countP_append (p := literal q) (l₁ := [-109, -111]) (l₂ := [-113, -114])
  have hm := merge_two (literal (valuationOf q) (1056)) (literal (valuationOf q) (1058)) (literal (valuationOf q) (1062)) (countLit q [-109, -111]) (countLit q [-113, -114]) (count1059 q) 2 2 (meaning1056 q) (meaning1058 q) (meaning1062 q) hs
  change valuationOf q 1056 = false ∨ valuationOf q 1058 = false ∨ valuationOf q 1062 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1056 = false ∨ valuation q 1058 = false ∨ valuation q 1062 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1063 = true := by
  have hs : count1063 q = (countLit q [-115]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-118])
  have hm := merge_right (literal (valuationOf q) (-118)) (literal (valuationOf q) (1063)) (countLit q [-115]) (countLit q [-118]) (count1063 q) 1 (meaningNeg118 q) (meaning1063 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1063 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1063 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1063 = true := by
  have hs : count1063 q = (countLit q [-115]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-118])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1063)) (countLit q [-115]) (countLit q [-118]) (count1063 q) 1 (meaningNeg115 q) (meaning1063 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1063 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1063 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 118 = true ∨ valuationOf q 1064 = true := by
  have hs : count1063 q = (countLit q [-115]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-118])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-118)) (literal (valuationOf q) (1064)) (countLit q [-115]) (countLit q [-118]) (count1063 q) 1 1 (meaningNeg115 q) (meaningNeg118 q) (meaning1064 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 118)) = false ∨ valuationOf q 1064 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 118 = true ∨ valuation q 1064 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 1065 = true := by
  have hs : count1065 q = (countLit q [-121]) + (countLit q [-122]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-122])
  have hm := merge_right (literal (valuationOf q) (-122)) (literal (valuationOf q) (1065)) (countLit q [-121]) (countLit q [-122]) (count1065 q) 1 (meaningNeg122 q) (meaning1065 q) hs
  change (! (valuationOf q 122)) = false ∨ valuationOf q 1065 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1065 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 1065 = true := by
  have hs : count1065 q = (countLit q [-121]) + (countLit q [-122]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-122])
  have hm := merge_left (literal (valuationOf q) (-121)) (literal (valuationOf q) (1065)) (countLit q [-121]) (countLit q [-122]) (count1065 q) 1 (meaningNeg121 q) (meaning1065 q) hs
  change (! (valuationOf q 121)) = false ∨ valuationOf q 1065 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 1065 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 122 = true ∨ valuationOf q 1066 = true := by
  have hs : count1065 q = (countLit q [-121]) + (countLit q [-122]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-122])
  have hm := merge_two (literal (valuationOf q) (-121)) (literal (valuationOf q) (-122)) (literal (valuationOf q) (1066)) (countLit q [-121]) (countLit q [-122]) (count1065 q) 1 1 (meaningNeg121 q) (meaningNeg122 q) (meaning1066 q) hs
  change (! (valuationOf q 121)) = false ∨ (! (valuationOf q 122)) = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 122 = true ∨ valuation q 1066 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1065 = false ∨ valuationOf q 1067 = true := by
  have hs : count1067 q = (countLit q [-115, -118]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-115, -118]) (l₂ := [-121, -122])
  have hm := merge_right (literal (valuationOf q) (1065)) (literal (valuationOf q) (1067)) (countLit q [-115, -118]) (countLit q [-121, -122]) (count1067 q) 1 (meaning1065 q) (meaning1067 q) hs
  change valuationOf q 1065 = false ∨ valuationOf q 1067 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1065 = false ∨ valuation q 1067 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1066 = false ∨ valuationOf q 1068 = true := by
  have hs : count1067 q = (countLit q [-115, -118]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-115, -118]) (l₂ := [-121, -122])
  have hm := merge_right (literal (valuationOf q) (1066)) (literal (valuationOf q) (1068)) (countLit q [-115, -118]) (countLit q [-121, -122]) (count1067 q) 2 (meaning1066 q) (meaning1068 q) hs
  change valuationOf q 1066 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1066 = false ∨ valuation q 1068 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1067 = true := by
  have hs : count1067 q = (countLit q [-115, -118]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-115, -118]) (l₂ := [-121, -122])
  have hm := merge_left (literal (valuationOf q) (1063)) (literal (valuationOf q) (1067)) (countLit q [-115, -118]) (countLit q [-121, -122]) (count1067 q) 1 (meaning1063 q) (meaning1067 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1067 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1067 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1068 = true := by
  have hs : count1067 q = (countLit q [-115, -118]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-115, -118]) (l₂ := [-121, -122])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1065)) (literal (valuationOf q) (1068)) (countLit q [-115, -118]) (countLit q [-121, -122]) (count1067 q) 1 1 (meaning1063 q) (meaning1065 q) (meaning1068 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1065 = false ∨ valuation q 1068 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1066 = false ∨ valuationOf q 1069 = true := by
  have hs : count1067 q = (countLit q [-115, -118]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-115, -118]) (l₂ := [-121, -122])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1066)) (literal (valuationOf q) (1069)) (countLit q [-115, -118]) (countLit q [-121, -122]) (count1067 q) 1 2 (meaning1063 q) (meaning1066 q) (meaning1069 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1066 = false ∨ valuationOf q 1069 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1066 = false ∨ valuation q 1069 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1068 = true := by
  have hs : count1067 q = (countLit q [-115, -118]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-115, -118]) (l₂ := [-121, -122])
  have hm := merge_left (literal (valuationOf q) (1064)) (literal (valuationOf q) (1068)) (countLit q [-115, -118]) (countLit q [-121, -122]) (count1067 q) 2 (meaning1064 q) (meaning1068 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1068 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1069 = true := by
  have hs : count1067 q = (countLit q [-115, -118]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-115, -118]) (l₂ := [-121, -122])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1065)) (literal (valuationOf q) (1069)) (countLit q [-115, -118]) (countLit q [-121, -122]) (count1067 q) 2 1 (meaning1064 q) (meaning1065 q) (meaning1069 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1065 = false ∨ valuationOf q 1069 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1065 = false ∨ valuation q 1069 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1066 = false ∨ valuationOf q 1070 = true := by
  have hs : count1067 q = (countLit q [-115, -118]) + (countLit q [-121, -122]) := List.countP_append (p := literal q) (l₁ := [-115, -118]) (l₂ := [-121, -122])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1066)) (literal (valuationOf q) (1070)) (countLit q [-115, -118]) (countLit q [-121, -122]) (count1067 q) 2 2 (meaning1064 q) (meaning1066 q) (meaning1070 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1066 = false ∨ valuationOf q 1070 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1066 = false ∨ valuation q 1070 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1067 = false ∨ valuationOf q 1071 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1067)) (literal (valuationOf q) (1071)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 1 (meaning1067 q) (meaning1071 q) hs
  change valuationOf q 1067 = false ∨ valuationOf q 1071 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1067 = false ∨ valuation q 1071 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1068 = false ∨ valuationOf q 1072 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1068)) (literal (valuationOf q) (1072)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 2 (meaning1068 q) (meaning1072 q) hs
  change valuationOf q 1068 = false ∨ valuationOf q 1072 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1068 = false ∨ valuation q 1072 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1069 = false ∨ valuationOf q 1073 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1069)) (literal (valuationOf q) (1073)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 3 (meaning1069 q) (meaning1073 q) hs
  change valuationOf q 1069 = false ∨ valuationOf q 1073 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1069 = false ∨ valuation q 1073 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1059 = false ∨ valuationOf q 1067 = false ∨ valuationOf q 1072 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1059)) (literal (valuationOf q) (1067)) (literal (valuationOf q) (1072)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 1 1 (meaning1059 q) (meaning1067 q) (meaning1072 q) hs
  change valuationOf q 1059 = false ∨ valuationOf q 1067 = false ∨ valuationOf q 1072 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1059 = false ∨ valuation q 1067 = false ∨ valuation q 1072 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1059 = false ∨ valuationOf q 1068 = false ∨ valuationOf q 1073 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1059)) (literal (valuationOf q) (1068)) (literal (valuationOf q) (1073)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 1 2 (meaning1059 q) (meaning1068 q) (meaning1073 q) hs
  change valuationOf q 1059 = false ∨ valuationOf q 1068 = false ∨ valuationOf q 1073 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1059 = false ∨ valuation q 1068 = false ∨ valuation q 1073 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1059 = false ∨ valuationOf q 1069 = false ∨ valuationOf q 1074 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1059)) (literal (valuationOf q) (1069)) (literal (valuationOf q) (1074)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 1 3 (meaning1059 q) (meaning1069 q) (meaning1074 q) hs
  change valuationOf q 1059 = false ∨ valuationOf q 1069 = false ∨ valuationOf q 1074 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1059 = false ∨ valuation q 1069 = false ∨ valuation q 1074 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1059 = false ∨ valuationOf q 1070 = false ∨ valuationOf q 1075 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1059)) (literal (valuationOf q) (1070)) (literal (valuationOf q) (1075)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 1 4 (meaning1059 q) (meaning1070 q) (meaning1075 q) hs
  change valuationOf q 1059 = false ∨ valuationOf q 1070 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1059 = false ∨ valuation q 1070 = false ∨ valuation q 1075 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1060 = false ∨ valuationOf q 1067 = false ∨ valuationOf q 1073 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1060)) (literal (valuationOf q) (1067)) (literal (valuationOf q) (1073)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 2 1 (meaning1060 q) (meaning1067 q) (meaning1073 q) hs
  change valuationOf q 1060 = false ∨ valuationOf q 1067 = false ∨ valuationOf q 1073 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1060 = false ∨ valuation q 1067 = false ∨ valuation q 1073 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1060 = false ∨ valuationOf q 1068 = false ∨ valuationOf q 1074 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1060)) (literal (valuationOf q) (1068)) (literal (valuationOf q) (1074)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 2 2 (meaning1060 q) (meaning1068 q) (meaning1074 q) hs
  change valuationOf q 1060 = false ∨ valuationOf q 1068 = false ∨ valuationOf q 1074 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1060 = false ∨ valuation q 1068 = false ∨ valuation q 1074 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1060 = false ∨ valuationOf q 1069 = false ∨ valuationOf q 1075 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1060)) (literal (valuationOf q) (1069)) (literal (valuationOf q) (1075)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 2 3 (meaning1060 q) (meaning1069 q) (meaning1075 q) hs
  change valuationOf q 1060 = false ∨ valuationOf q 1069 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1060 = false ∨ valuation q 1069 = false ∨ valuation q 1075 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E097.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112097
