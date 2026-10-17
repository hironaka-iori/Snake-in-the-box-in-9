import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1511 = true := by
  have hs : count1509 q = (countLit q [-38, -40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1511)) (countLit q [-38, -40]) (countLit q [-42, -44]) (count1509 q) 1 2 (meaning1505 q) (meaning1508 q) (meaning1511 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1508 = false ∨ valuation q 1511 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1510 = true := by
  have hs : count1509 q = (countLit q [-38, -40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-42, -44])
  have hm := merge_left (literal (valuationOf q) (1506)) (literal (valuationOf q) (1510)) (countLit q [-38, -40]) (countLit q [-42, -44]) (count1509 q) 2 (meaning1506 q) (meaning1510 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1510 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1511 = true := by
  have hs : count1509 q = (countLit q [-38, -40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1511)) (countLit q [-38, -40]) (countLit q [-42, -44]) (count1509 q) 2 1 (meaning1506 q) (meaning1507 q) (meaning1511 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1507 = false ∨ valuation q 1511 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1512 = true := by
  have hs : count1509 q = (countLit q [-38, -40]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -40]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1512)) (countLit q [-38, -40]) (countLit q [-42, -44]) (count1509 q) 2 2 (meaning1506 q) (meaning1508 q) (meaning1512 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = false ∨ valuation q 1512 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1513 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1513)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 1 (meaning1509 q) (meaning1513 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1513 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_right (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 2 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1515 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_right (literal (valuationOf q) (1511)) (literal (valuationOf q) (1515)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 3 (meaning1511 q) (meaning1515 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1515 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1516 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1516)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 4 (meaning1512 q) (meaning1516 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1516 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1513 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_left (literal (valuationOf q) (1502)) (literal (valuationOf q) (1513)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 1 (meaning1502 q) (meaning1513 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1513 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1514)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 1 1 (meaning1502 q) (meaning1509 q) (meaning1514 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1509 = false ∨ valuation q 1514 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1515)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 1 2 (meaning1502 q) (meaning1510 q) (meaning1515 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1510 = false ∨ valuation q 1515 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1516)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 1 3 (meaning1502 q) (meaning1511 q) (meaning1516 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1511 = false ∨ valuation q 1516 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1517 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1517)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 1 4 (meaning1502 q) (meaning1512 q) (meaning1517 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1512 = false ∨ valuation q 1517 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_left (literal (valuationOf q) (1503)) (literal (valuationOf q) (1514)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 2 (meaning1503 q) (meaning1514 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1514 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1515 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1515)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 2 1 (meaning1503 q) (meaning1509 q) (meaning1515 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1509 = false ∨ valuation q 1515 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1516)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 2 2 (meaning1503 q) (meaning1510 q) (meaning1516 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1510 = false ∨ valuation q 1516 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1517)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 2 3 (meaning1503 q) (meaning1511 q) (meaning1517 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1511 = false ∨ valuation q 1517 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1518 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1518)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 2 4 (meaning1503 q) (meaning1512 q) (meaning1518 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1512 = false ∨ valuation q 1518 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1515 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_left (literal (valuationOf q) (1504)) (literal (valuationOf q) (1515)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 3 (meaning1504 q) (meaning1515 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1515 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1516 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1516)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 3 1 (meaning1504 q) (meaning1509 q) (meaning1516 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1509 = false ∨ valuation q 1516 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1517)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 3 2 (meaning1504 q) (meaning1510 q) (meaning1517 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1510 = false ∨ valuation q 1517 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1518 = true := by
  have hs : count1513 q = (countLit q [-32, -35, -36]) + (countLit q [-38, -40, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36]) (l₂ := [-38, -40, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1518)) (countLit q [-32, -35, -36]) (countLit q [-38, -40, -42, -44]) (count1513 q) 3 3 (meaning1504 q) (meaning1511 q) (meaning1518 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1511 = false ∨ valuation q 1518 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1520 = true := by
  have hs : count1520 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1520)) (countLit q [-46]) (countLit q [-48]) (count1520 q) 1 (meaningNeg48 q) (meaning1520 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1520 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1520 = true := by
  have hs : count1520 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1520)) (countLit q [-46]) (countLit q [-48]) (count1520 q) 1 (meaningNeg46 q) (meaning1520 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1520 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 48 = true ∨ valuationOf q 1521 = true := by
  have hs : count1520 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (1521)) (countLit q [-46]) (countLit q [-48]) (count1520 q) 1 1 (meaningNeg46 q) (meaningNeg48 q) (meaning1521 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 1521 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1522 = true := by
  have hs : count1522 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1522)) (countLit q [-51]) (countLit q [-52]) (count1522 q) 1 (meaningNeg52 q) (meaning1522 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1522 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1522 = true := by
  have hs : count1522 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (1522)) (countLit q [-51]) (countLit q [-52]) (count1522 q) 1 (meaningNeg51 q) (meaning1522 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1522 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 52 = true ∨ valuationOf q 1523 = true := by
  have hs : count1522 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (1523)) (countLit q [-51]) (countLit q [-52]) (count1522 q) 1 1 (meaningNeg51 q) (meaningNeg52 q) (meaning1523 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 1523 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_right (literal (valuationOf q) (1522)) (literal (valuationOf q) (1524)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1524 q) 1 (meaning1522 q) (meaning1524 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1524 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_right (literal (valuationOf q) (1523)) (literal (valuationOf q) (1525)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1524 q) 2 (meaning1523 q) (meaning1525 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1525 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_left (literal (valuationOf q) (1520)) (literal (valuationOf q) (1524)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1524 q) 1 (meaning1520 q) (meaning1524 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1524 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-46, -48]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1525)) (countLit q [-46, -48]) (countLit q [-51, -52]) (count1524 q) 1 1 (meaning1520 q) (meaning1522 q) (meaning1525 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1522 = false ∨ valuation q 1525 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E004.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112004
