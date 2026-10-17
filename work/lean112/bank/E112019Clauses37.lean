import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_right (literal (valuationOf q) (-11)) (literal (valuationOf q) (1480)) (countLit q [-9]) (countLit q [-11]) (count1480 q) 1 (meaningNeg11 q) (meaning1480 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1480 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (1480)) (countLit q [-9]) (countLit q [-11]) (count1480 q) 1 (meaningNeg9 q) (meaning1480 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1480 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 11 = true ∨ valuationOf q 1481 = true := by
  have hs : count1480 q = (countLit q [-9]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-11])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-11)) (literal (valuationOf q) (1481)) (countLit q [-9]) (countLit q [-11]) (count1480 q) 1 1 (meaningNeg9 q) (meaningNeg11 q) (meaning1481 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 11)) = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 11 = true ∨ valuation q 1481 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-14]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16])
  have hm := merge_right (literal (valuationOf q) (-16)) (literal (valuationOf q) (1482)) (countLit q [-14]) (countLit q [-16]) (count1482 q) 1 (meaningNeg16 q) (meaning1482 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1482 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-14]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1482)) (countLit q [-14]) (countLit q [-16]) (count1482 q) 1 (meaningNeg14 q) (meaning1482 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1482 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 16 = true ∨ valuationOf q 1483 = true := by
  have hs : count1482 q = (countLit q [-14]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-16])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-16)) (literal (valuationOf q) (1483)) (countLit q [-14]) (countLit q [-16]) (count1482 q) 1 1 (meaningNeg14 q) (meaningNeg16 q) (meaning1483 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 16)) = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 16 = true ∨ valuation q 1483 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1484 = true := by
  have hs : count1484 q = (countLit q [-9, -11]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-14, -16])
  have hm := merge_right (literal (valuationOf q) (1482)) (literal (valuationOf q) (1484)) (countLit q [-9, -11]) (countLit q [-14, -16]) (count1484 q) 1 (meaning1482 q) (meaning1484 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1484 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-9, -11]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-14, -16])
  have hm := merge_right (literal (valuationOf q) (1483)) (literal (valuationOf q) (1485)) (countLit q [-9, -11]) (countLit q [-14, -16]) (count1484 q) 2 (meaning1483 q) (meaning1485 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1485 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1484 = true := by
  have hs : count1484 q = (countLit q [-9, -11]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-14, -16])
  have hm := merge_left (literal (valuationOf q) (1480)) (literal (valuationOf q) (1484)) (countLit q [-9, -11]) (countLit q [-14, -16]) (count1484 q) 1 (meaning1480 q) (meaning1484 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1484 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-9, -11]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-14, -16])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1485)) (countLit q [-9, -11]) (countLit q [-14, -16]) (count1484 q) 1 1 (meaning1480 q) (meaning1482 q) (meaning1485 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1482 = false ∨ valuation q 1485 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1486 = true := by
  have hs : count1484 q = (countLit q [-9, -11]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-14, -16])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1486)) (countLit q [-9, -11]) (countLit q [-14, -16]) (count1484 q) 1 2 (meaning1480 q) (meaning1483 q) (meaning1486 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1483 = false ∨ valuation q 1486 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-9, -11]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-14, -16])
  have hm := merge_left (literal (valuationOf q) (1481)) (literal (valuationOf q) (1485)) (countLit q [-9, -11]) (countLit q [-14, -16]) (count1484 q) 2 (meaning1481 q) (meaning1485 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1485 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1486 = true := by
  have hs : count1484 q = (countLit q [-9, -11]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-14, -16])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1486)) (countLit q [-9, -11]) (countLit q [-14, -16]) (count1484 q) 2 1 (meaning1481 q) (meaning1482 q) (meaning1486 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1482 = false ∨ valuation q 1486 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1487 = true := by
  have hs : count1484 q = (countLit q [-9, -11]) + (countLit q [-14, -16]) := List.countP_append (p := literal q) (l₁ := [-9, -11]) (l₂ := [-14, -16])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1487)) (countLit q [-9, -11]) (countLit q [-14, -16]) (count1484 q) 2 2 (meaning1481 q) (meaning1483 q) (meaning1487 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1483 = false ∨ valuation q 1487 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_right (literal (valuationOf q) (1484)) (literal (valuationOf q) (1488)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 1 (meaning1484 q) (meaning1488 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1488 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_right (literal (valuationOf q) (1485)) (literal (valuationOf q) (1489)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 2 (meaning1485 q) (meaning1489 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1489 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_right (literal (valuationOf q) (1486)) (literal (valuationOf q) (1490)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 3 (meaning1486 q) (meaning1490 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1490 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1491 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_right (literal (valuationOf q) (1487)) (literal (valuationOf q) (1491)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 4 (meaning1487 q) (meaning1491 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1491 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_left (literal (valuationOf q) (1477)) (literal (valuationOf q) (1488)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 1 (meaning1477 q) (meaning1488 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1488 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1489)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 1 1 (meaning1477 q) (meaning1484 q) (meaning1489 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1484 = false ∨ valuation q 1489 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1490)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 1 2 (meaning1477 q) (meaning1485 q) (meaning1490 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1485 = false ∨ valuation q 1490 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1491 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1486)) (literal (valuationOf q) (1491)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 1 3 (meaning1477 q) (meaning1486 q) (meaning1491 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1486 = false ∨ valuation q 1491 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1492 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1492)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 1 4 (meaning1477 q) (meaning1487 q) (meaning1492 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1487 = false ∨ valuation q 1492 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_left (literal (valuationOf q) (1478)) (literal (valuationOf q) (1489)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 2 (meaning1478 q) (meaning1489 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1489 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1490)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 2 1 (meaning1478 q) (meaning1484 q) (meaning1490 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1484 = false ∨ valuation q 1490 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1491 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1491)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 2 2 (meaning1478 q) (meaning1485 q) (meaning1491 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1485 = false ∨ valuation q 1491 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1492 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1486)) (literal (valuationOf q) (1492)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 2 3 (meaning1478 q) (meaning1486 q) (meaning1492 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1486 = false ∨ valuation q 1492 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_left (literal (valuationOf q) (1479)) (literal (valuationOf q) (1490)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 3 (meaning1479 q) (meaning1490 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1490 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1492 = true := by
  have hs : count1488 q = (countLit q [-2, -5, -7]) + (countLit q [-9, -11, -14, -16]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7]) (l₂ := [-9, -11, -14, -16])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1492)) (countLit q [-2, -5, -7]) (countLit q [-9, -11, -14, -16]) (count1488 q) 3 2 (meaning1479 q) (meaning1485 q) (meaning1492 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1485 = false ∨ valuation q 1492 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1495 = true := by
  have hs : count1495 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1495)) (countLit q [-19]) (countLit q [-21]) (count1495 q) 1 (meaningNeg21 q) (meaning1495 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1495 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1495 = true := by
  have hs : count1495 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1495)) (countLit q [-19]) (countLit q [-21]) (count1495 q) 1 (meaningNeg19 q) (meaning1495 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1495 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 21 = true ∨ valuationOf q 1496 = true := by
  have hs : count1495 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (1496)) (countLit q [-19]) (countLit q [-21]) (count1495 q) 1 1 (meaningNeg19 q) (meaningNeg21 q) (meaning1496 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 21 = true ∨ valuation q 1496 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E019.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112019
