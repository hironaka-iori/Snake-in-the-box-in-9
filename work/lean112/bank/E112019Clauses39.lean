import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1511 = true := by
  have hs : count1508 q = (countLit q [-18, -19, -21]) + (countLit q [-24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -19, -21]) (l₂ := [-24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1511)) (countLit q [-18, -19, -21]) (countLit q [-24, -26, -28, -31]) (count1508 q) 3 1 (meaning1499 q) (meaning1504 q) (meaning1511 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1504 = false ∨ valuation q 1511 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1515 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1515)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 1 (meaning1508 q) (meaning1515 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1515 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1516 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 2 (meaning1509 q) (meaning1516 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1516 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1517 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1510)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 3 (meaning1510 q) (meaning1517 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1517 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1518 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1511)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 4 (meaning1511 q) (meaning1518 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1518 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1519 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1519)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 5 (meaning1512 q) (meaning1519 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1519 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1516 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 1 1 (meaning1488 q) (meaning1508 q) (meaning1516 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1508 = false ∨ valuation q 1516 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1517 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 1 2 (meaning1488 q) (meaning1509 q) (meaning1517 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1509 = false ∨ valuation q 1517 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1518 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 1 3 (meaning1488 q) (meaning1510 q) (meaning1518 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1510 = false ∨ valuation q 1518 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1519 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1519)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 1 4 (meaning1488 q) (meaning1511 q) (meaning1519 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1511 = false ∨ valuation q 1519 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1520 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1520)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 1 5 (meaning1488 q) (meaning1512 q) (meaning1520 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1512 = false ∨ valuation q 1520 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1516 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1489)) (literal (valuationOf q) (1516)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 2 (meaning1489 q) (meaning1516 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1516 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1517 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 2 1 (meaning1489 q) (meaning1508 q) (meaning1517 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1508 = false ∨ valuation q 1517 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1518 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 2 2 (meaning1489 q) (meaning1509 q) (meaning1518 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1509 = false ∨ valuation q 1518 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1519 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1519)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 2 3 (meaning1489 q) (meaning1510 q) (meaning1519 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1510 = false ∨ valuation q 1519 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1520 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1520)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 2 4 (meaning1489 q) (meaning1511 q) (meaning1520 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1511 = false ∨ valuation q 1520 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1521 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1521)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 2 5 (meaning1489 q) (meaning1512 q) (meaning1521 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1512 = false ∨ valuation q 1521 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1517 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1490)) (literal (valuationOf q) (1517)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 3 (meaning1490 q) (meaning1517 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1517 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1518 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 3 1 (meaning1490 q) (meaning1508 q) (meaning1518 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1508 = false ∨ valuation q 1518 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1519 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1519)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 3 2 (meaning1490 q) (meaning1509 q) (meaning1519 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1509 = false ∨ valuation q 1519 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1520 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1520)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 3 3 (meaning1490 q) (meaning1510 q) (meaning1520 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1510 = false ∨ valuation q 1520 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1521 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1521)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 3 4 (meaning1490 q) (meaning1511 q) (meaning1521 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1511 = false ∨ valuation q 1521 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1522 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1522)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 3 5 (meaning1490 q) (meaning1512 q) (meaning1522 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1512 = false ∨ valuation q 1522 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1518 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1491)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 4 (meaning1491 q) (meaning1518 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1518 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1519 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1519)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 4 1 (meaning1491 q) (meaning1508 q) (meaning1519 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1508 = false ∨ valuation q 1519 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1520 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1520)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 4 2 (meaning1491 q) (meaning1509 q) (meaning1520 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1509 = false ∨ valuation q 1520 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1521 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1521)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 4 3 (meaning1491 q) (meaning1510 q) (meaning1521 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1510 = false ∨ valuation q 1521 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1522 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1522)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 4 4 (meaning1491 q) (meaning1511 q) (meaning1522 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1511 = false ∨ valuation q 1522 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1523 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1523)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 4 5 (meaning1491 q) (meaning1512 q) (meaning1523 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1512 = false ∨ valuation q 1523 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1520 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1520)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 5 1 (meaning1492 q) (meaning1508 q) (meaning1520 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1508 = false ∨ valuation q 1520 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1521 = true := by
  have hs : count1515 q = (countLit q [-2, -5, -7, -9, -11, -14, -16]) + (countLit q [-18, -19, -21, -24, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16]) (l₂ := [-18, -19, -21, -24, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1521)) (countLit q [-2, -5, -7, -9, -11, -14, -16]) (countLit q [-18, -19, -21, -24, -26, -28, -31]) (count1515 q) 5 2 (meaning1492 q) (meaning1509 q) (meaning1521 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1509 = false ∨ valuation q 1521 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1529 = true := by
  have hs : count1529 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (1529)) (countLit q [-35]) (countLit q [-36]) (count1529 q) 1 (meaningNeg36 q) (meaning1529 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1529 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E019.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112019
