import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1524 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1524)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 4 2 (meaning1491 q) (meaning1512 q) (meaning1524 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1512 = false ∨ valuation q 1524 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1525 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1525)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 4 3 (meaning1491 q) (meaning1513 q) (meaning1525 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1513 = false ∨ valuation q 1525 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1526 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1526)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 4 4 (meaning1491 q) (meaning1514 q) (meaning1526 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1514 = false ∨ valuation q 1526 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1527 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1527)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 4 5 (meaning1491 q) (meaning1515 q) (meaning1527 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1515 = false ∨ valuation q 1527 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1528 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1528)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 4 6 (meaning1491 q) (meaning1516 q) (meaning1528 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1516 = false ∨ valuation q 1528 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1529 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1529)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 4 7 (meaning1491 q) (meaning1517 q) (meaning1529 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1517 = false ∨ valuation q 1529 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1524 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1524)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 5 1 (meaning1492 q) (meaning1511 q) (meaning1524 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1511 = false ∨ valuation q 1524 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1525 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1525)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 5 2 (meaning1492 q) (meaning1512 q) (meaning1525 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1512 = false ∨ valuation q 1525 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1526 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1526)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 5 3 (meaning1492 q) (meaning1513 q) (meaning1526 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1513 = false ∨ valuation q 1526 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1527 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1527)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 5 4 (meaning1492 q) (meaning1514 q) (meaning1527 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1514 = false ∨ valuation q 1527 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1528 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1528)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 5 5 (meaning1492 q) (meaning1515 q) (meaning1528 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1515 = false ∨ valuation q 1528 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1541 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1541)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 1 7 (meaning1461 q) (meaning1525 q) (meaning1541 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1525 = false ∨ valuation q 1541 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1540 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1540)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 2 5 (meaning1462 q) (meaning1523 q) (meaning1540 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1523 = false ∨ valuation q 1540 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1541 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1541)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 2 6 (meaning1462 q) (meaning1524 q) (meaning1541 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1524 = false ∨ valuation q 1541 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1542 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1542)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 2 7 (meaning1462 q) (meaning1525 q) (meaning1542 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1525 = false ∨ valuation q 1542 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1543 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1543)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 2 8 (meaning1462 q) (meaning1526 q) (meaning1543 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1526 = false ∨ valuation q 1543 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1544 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1544)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 2 9 (meaning1462 q) (meaning1527 q) (meaning1544 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1527 = false ∨ valuation q 1544 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1545 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1545)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 2 10 (meaning1462 q) (meaning1528 q) (meaning1545 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1528 = false ∨ valuation q 1545 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1546 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1546)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 2 11 (meaning1462 q) (meaning1529 q) (meaning1546 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1529 = false ∨ valuation q 1546 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1539 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1539)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 3 3 (meaning1463 q) (meaning1521 q) (meaning1539 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1521 = false ∨ valuation q 1539 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1540 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1540)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 3 4 (meaning1463 q) (meaning1522 q) (meaning1540 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1522 = false ∨ valuation q 1540 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1541 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1541)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 3 5 (meaning1463 q) (meaning1523 q) (meaning1541 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1523 = false ∨ valuation q 1541 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1542 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1542)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 3 6 (meaning1463 q) (meaning1524 q) (meaning1542 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1524 = false ∨ valuation q 1542 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1543 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1543)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 3 7 (meaning1463 q) (meaning1525 q) (meaning1543 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1525 = false ∨ valuation q 1543 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1544 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1544)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 3 8 (meaning1463 q) (meaning1526 q) (meaning1544 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1526 = false ∨ valuation q 1544 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1545 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1545)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 3 9 (meaning1463 q) (meaning1527 q) (meaning1545 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1527 = false ∨ valuation q 1545 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1546 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1546)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 3 10 (meaning1463 q) (meaning1528 q) (meaning1546 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1528 = false ∨ valuation q 1546 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1539 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1539)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 4 2 (meaning1464 q) (meaning1520 q) (meaning1539 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1520 = false ∨ valuation q 1539 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1540 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1540)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 4 3 (meaning1464 q) (meaning1521 q) (meaning1540 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1521 = false ∨ valuation q 1540 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1541 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1541)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 4 4 (meaning1464 q) (meaning1522 q) (meaning1541 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1522 = false ∨ valuation q 1541 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1542 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1542)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 4 5 (meaning1464 q) (meaning1523 q) (meaning1542 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1523 = false ∨ valuation q 1542 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1543 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1543)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 4 6 (meaning1464 q) (meaning1524 q) (meaning1543 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1524 = false ∨ valuation q 1543 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E158.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112158
