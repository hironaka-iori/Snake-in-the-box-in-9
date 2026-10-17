import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1060 = false ∨ valuationOf q 1070 = false ∨ valuationOf q 1076 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1060)) (literal (valuationOf q) (1070)) (literal (valuationOf q) (1076)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 2 4 (meaning1060 q) (meaning1070 q) (meaning1076 q) hs
  change valuationOf q 1060 = false ∨ valuationOf q 1070 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1060 = false ∨ valuation q 1070 = false ∨ valuation q 1076 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1061 = false ∨ valuationOf q 1067 = false ∨ valuationOf q 1074 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1061)) (literal (valuationOf q) (1067)) (literal (valuationOf q) (1074)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 3 1 (meaning1061 q) (meaning1067 q) (meaning1074 q) hs
  change valuationOf q 1061 = false ∨ valuationOf q 1067 = false ∨ valuationOf q 1074 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1061 = false ∨ valuation q 1067 = false ∨ valuation q 1074 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1061 = false ∨ valuationOf q 1068 = false ∨ valuationOf q 1075 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1061)) (literal (valuationOf q) (1068)) (literal (valuationOf q) (1075)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 3 2 (meaning1061 q) (meaning1068 q) (meaning1075 q) hs
  change valuationOf q 1061 = false ∨ valuationOf q 1068 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1061 = false ∨ valuation q 1068 = false ∨ valuation q 1075 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1061 = false ∨ valuationOf q 1069 = false ∨ valuationOf q 1076 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1061)) (literal (valuationOf q) (1069)) (literal (valuationOf q) (1076)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 3 3 (meaning1061 q) (meaning1069 q) (meaning1076 q) hs
  change valuationOf q 1061 = false ∨ valuationOf q 1069 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1061 = false ∨ valuation q 1069 = false ∨ valuation q 1076 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1061 = false ∨ valuationOf q 1070 = false ∨ valuationOf q 1077 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1061)) (literal (valuationOf q) (1070)) (literal (valuationOf q) (1077)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 3 4 (meaning1061 q) (meaning1070 q) (meaning1077 q) hs
  change valuationOf q 1061 = false ∨ valuationOf q 1070 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1061 = false ∨ valuation q 1070 = false ∨ valuation q 1077 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1062 = false ∨ valuationOf q 1067 = false ∨ valuationOf q 1075 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1062)) (literal (valuationOf q) (1067)) (literal (valuationOf q) (1075)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 4 1 (meaning1062 q) (meaning1067 q) (meaning1075 q) hs
  change valuationOf q 1062 = false ∨ valuationOf q 1067 = false ∨ valuationOf q 1075 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1062 = false ∨ valuation q 1067 = false ∨ valuation q 1075 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1062 = false ∨ valuationOf q 1068 = false ∨ valuationOf q 1076 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1062)) (literal (valuationOf q) (1068)) (literal (valuationOf q) (1076)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 4 2 (meaning1062 q) (meaning1068 q) (meaning1076 q) hs
  change valuationOf q 1062 = false ∨ valuationOf q 1068 = false ∨ valuationOf q 1076 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1062 = false ∨ valuation q 1068 = false ∨ valuation q 1076 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1062 = false ∨ valuationOf q 1069 = false ∨ valuationOf q 1077 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1062)) (literal (valuationOf q) (1069)) (literal (valuationOf q) (1077)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 4 3 (meaning1062 q) (meaning1069 q) (meaning1077 q) hs
  change valuationOf q 1062 = false ∨ valuationOf q 1069 = false ∨ valuationOf q 1077 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1062 = false ∨ valuation q 1069 = false ∨ valuation q 1077 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1062 = false ∨ valuationOf q 1070 = false ∨ valuationOf q 1078 = true := by
  have hs : count1071 q = (countLit q [-109, -111, -113, -114]) + (countLit q [-115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-109, -111, -113, -114]) (l₂ := [-115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1062)) (literal (valuationOf q) (1070)) (literal (valuationOf q) (1078)) (countLit q [-109, -111, -113, -114]) (countLit q [-115, -118, -121, -122]) (count1071 q) 4 4 (meaning1062 q) (meaning1070 q) (meaning1078 q) hs
  change valuationOf q 1062 = false ∨ valuationOf q 1070 = false ∨ valuationOf q 1078 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1062 = false ∨ valuation q 1070 = false ∨ valuation q 1078 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1080 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1072)) (literal (valuationOf q) (1080)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 2 (meaning1072 q) (meaning1080 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1080 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1080 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1073 = false ∨ valuationOf q 1081 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1073)) (literal (valuationOf q) (1081)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 3 (meaning1073 q) (meaning1081 q) hs
  change valuationOf q 1073 = false ∨ valuationOf q 1081 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1073 = false ∨ valuation q 1081 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1074 = false ∨ valuationOf q 1082 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1074)) (literal (valuationOf q) (1082)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 4 (meaning1074 q) (meaning1082 q) hs
  change valuationOf q 1074 = false ∨ valuationOf q 1082 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1074 = false ∨ valuation q 1082 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1075 = false ∨ valuationOf q 1083 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1075)) (literal (valuationOf q) (1083)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 5 (meaning1075 q) (meaning1083 q) hs
  change valuationOf q 1075 = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1075 = false ∨ valuation q 1083 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1076 = false ∨ valuationOf q 1084 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1076)) (literal (valuationOf q) (1084)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 6 (meaning1076 q) (meaning1084 q) hs
  change valuationOf q 1076 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1076 = false ∨ valuation q 1084 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1077 = false ∨ valuationOf q 1085 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_right (literal (valuationOf q) (1077)) (literal (valuationOf q) (1085)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 7 (meaning1077 q) (meaning1085 q) hs
  change valuationOf q 1077 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1077 = false ∨ valuation q 1085 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1081 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1072)) (literal (valuationOf q) (1081)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 1 2 (meaning1047 q) (meaning1072 q) (meaning1081 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1081 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1072 = false ∨ valuation q 1081 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1082 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1073)) (literal (valuationOf q) (1082)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 1 3 (meaning1047 q) (meaning1073 q) (meaning1082 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1082 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1073 = false ∨ valuation q 1082 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1083 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1074)) (literal (valuationOf q) (1083)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 1 4 (meaning1047 q) (meaning1074 q) (meaning1083 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1074 = false ∨ valuation q 1083 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1075 = false ∨ valuationOf q 1084 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1075)) (literal (valuationOf q) (1084)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 1 5 (meaning1047 q) (meaning1075 q) (meaning1084 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1075 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1075 = false ∨ valuation q 1084 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1076 = false ∨ valuationOf q 1085 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1076)) (literal (valuationOf q) (1085)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 1 6 (meaning1047 q) (meaning1076 q) (meaning1085 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1076 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1076 = false ∨ valuation q 1085 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1077 = false ∨ valuationOf q 1086 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1077)) (literal (valuationOf q) (1086)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 1 7 (meaning1047 q) (meaning1077 q) (meaning1086 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1077 = false ∨ valuationOf q 1086 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1077 = false ∨ valuation q 1086 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1078 = false ∨ valuationOf q 1087 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1078)) (literal (valuationOf q) (1087)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 1 8 (meaning1047 q) (meaning1078 q) (meaning1087 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1078 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1078 = false ∨ valuation q 1087 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1071 = false ∨ valuationOf q 1081 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1071)) (literal (valuationOf q) (1081)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 2 1 (meaning1048 q) (meaning1071 q) (meaning1081 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1071 = false ∨ valuationOf q 1081 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1071 = false ∨ valuation q 1081 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1082 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1072)) (literal (valuationOf q) (1082)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 2 2 (meaning1048 q) (meaning1072 q) (meaning1082 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1082 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1072 = false ∨ valuation q 1082 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1083 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1073)) (literal (valuationOf q) (1083)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 2 3 (meaning1048 q) (meaning1073 q) (meaning1083 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1073 = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1073 = false ∨ valuation q 1083 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1084 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1074)) (literal (valuationOf q) (1084)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 2 4 (meaning1048 q) (meaning1074 q) (meaning1084 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1074 = false ∨ valuationOf q 1084 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1074 = false ∨ valuation q 1084 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1075 = false ∨ valuationOf q 1085 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1075)) (literal (valuationOf q) (1085)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 2 5 (meaning1048 q) (meaning1075 q) (meaning1085 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1075 = false ∨ valuationOf q 1085 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1075 = false ∨ valuation q 1085 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1076 = false ∨ valuationOf q 1086 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1076)) (literal (valuationOf q) (1086)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 2 6 (meaning1048 q) (meaning1076 q) (meaning1086 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1076 = false ∨ valuationOf q 1086 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1076 = false ∨ valuation q 1086 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1077 = false ∨ valuationOf q 1087 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1077)) (literal (valuationOf q) (1087)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 2 7 (meaning1048 q) (meaning1077 q) (meaning1087 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1077 = false ∨ valuationOf q 1087 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1077 = false ∨ valuation q 1087 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1078 = false ∨ valuationOf q 1088 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1078)) (literal (valuationOf q) (1088)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 2 8 (meaning1048 q) (meaning1078 q) (meaning1088 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1078 = false ∨ valuationOf q 1088 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1078 = false ∨ valuation q 1088 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1071 = false ∨ valuationOf q 1082 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1049)) (literal (valuationOf q) (1071)) (literal (valuationOf q) (1082)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 3 1 (meaning1049 q) (meaning1071 q) (meaning1082 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1071 = false ∨ valuationOf q 1082 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1071 = false ∨ valuation q 1082 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1083 = true := by
  have hs : count1079 q = (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) + (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -95, -97, -100, -101, -105, -106, -108]) (l₂ := [-109, -111, -113, -114, -115, -118, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1049)) (literal (valuationOf q) (1072)) (literal (valuationOf q) (1083)) (countLit q [-94, -95, -97, -100, -101, -105, -106, -108]) (countLit q [-109, -111, -113, -114, -115, -118, -121, -122]) (count1079 q) 3 2 (meaning1049 q) (meaning1072 q) (meaning1083 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1072 = false ∨ valuationOf q 1083 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1072 = false ∨ valuation q 1083 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E097.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112097
