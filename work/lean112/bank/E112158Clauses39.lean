import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1544 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1544)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 4 7 (meaning1464 q) (meaning1525 q) (meaning1544 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1525 = false ∨ valuation q 1544 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1545 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1545)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 4 8 (meaning1464 q) (meaning1526 q) (meaning1545 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1526 = false ∨ valuation q 1545 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1546 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1546)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 4 9 (meaning1464 q) (meaning1527 q) (meaning1546 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1527 = false ∨ valuation q 1546 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1540 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1540)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 5 2 (meaning1465 q) (meaning1520 q) (meaning1540 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1520 = false ∨ valuation q 1540 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1541 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1541)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 5 3 (meaning1465 q) (meaning1521 q) (meaning1541 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1521 = false ∨ valuation q 1541 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1542 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1542)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 5 4 (meaning1465 q) (meaning1522 q) (meaning1542 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1522 = false ∨ valuation q 1542 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1543 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1543)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 5 5 (meaning1465 q) (meaning1523 q) (meaning1543 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1523 = false ∨ valuation q 1543 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1544 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1544)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 5 6 (meaning1465 q) (meaning1524 q) (meaning1544 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1524 = false ∨ valuation q 1544 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1545 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1545)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 5 7 (meaning1465 q) (meaning1525 q) (meaning1545 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1525 = false ∨ valuation q 1545 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1546 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1546)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 5 8 (meaning1465 q) (meaning1526 q) (meaning1546 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1526 = false ∨ valuation q 1546 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1541 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1541)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 6 2 (meaning1466 q) (meaning1520 q) (meaning1541 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1520 = false ∨ valuation q 1541 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1542 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1542)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 6 3 (meaning1466 q) (meaning1521 q) (meaning1542 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1521 = false ∨ valuation q 1542 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1543 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1543)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 6 4 (meaning1466 q) (meaning1522 q) (meaning1543 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1522 = false ∨ valuation q 1543 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1544 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1544)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 6 5 (meaning1466 q) (meaning1523 q) (meaning1544 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1523 = false ∨ valuation q 1544 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1545 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1545)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 6 6 (meaning1466 q) (meaning1524 q) (meaning1545 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1524 = false ∨ valuation q 1545 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1546 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1546)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 6 7 (meaning1466 q) (meaning1525 q) (meaning1546 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1525 = false ∨ valuation q 1546 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1542 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1542)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 7 2 (meaning1467 q) (meaning1520 q) (meaning1542 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1520 = false ∨ valuation q 1542 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1543 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1543)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 7 3 (meaning1467 q) (meaning1521 q) (meaning1543 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1521 = false ∨ valuation q 1543 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1544 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1544)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 7 4 (meaning1467 q) (meaning1522 q) (meaning1544 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1522 = false ∨ valuation q 1544 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1546 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1546)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 7 6 (meaning1467 q) (meaning1524 q) (meaning1546 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1524 = false ∨ valuation q 1546 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1547 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1547)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 7 7 (meaning1467 q) (meaning1525 q) (meaning1547 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1525 = false ∨ valuation q 1547 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1546 = true := by
  have hs : count1534 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) + (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (l₂ := [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1546)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30]) (countLit q [-32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (count1534 q) 8 5 (meaning1468 q) (meaning1523 q) (meaning1546 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1523 = false ∨ valuation q 1546 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1553)) (countLit q [-61]) (countLit q [-63]) (count1553 q) 1 (meaningNeg63 q) (meaning1553 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1553 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1553)) (countLit q [-61]) (countLit q [-63]) (count1553 q) 1 (meaningNeg61 q) (meaning1553 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1553 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1554)) (countLit q [-61]) (countLit q [-63]) (count1553 q) 1 1 (meaningNeg61 q) (meaningNeg63 q) (meaning1554 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 63 = true ∨ valuation q 1554 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1553)) (literal (valuationOf q) (1555)) (countLit q [-59]) (countLit q [-61, -63]) (count1555 q) 1 (meaning1553 q) (meaning1555 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1555 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1554)) (literal (valuationOf q) (1556)) (countLit q [-59]) (countLit q [-61, -63]) (count1555 q) 2 (meaning1554 q) (meaning1556 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1556 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1555)) (countLit q [-59]) (countLit q [-61, -63]) (count1555 q) 1 (meaningNeg59 q) (meaning1555 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1555 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1553 = false ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1556)) (countLit q [-59]) (countLit q [-61, -63]) (count1555 q) 1 1 (meaningNeg59 q) (meaning1553 q) (meaning1556 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1553 = false ∨ valuation q 1556 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1554 = false ∨ valuationOf q 1557 = true := by
  have hs : count1555 q = (countLit q [-59]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -63])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1557)) (countLit q [-59]) (countLit q [-61, -63]) (count1555 q) 1 2 (meaningNeg59 q) (meaning1554 q) (meaning1557 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1554 = false ∨ valuation q 1557 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (1558)) (countLit q [-65]) (countLit q [-68]) (count1558 q) 1 (meaningNeg68 q) (meaning1558 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1558 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1558 = true := by
  have hs : count1558 q = (countLit q [-65]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1558)) (countLit q [-65]) (countLit q [-68]) (count1558 q) 1 (meaningNeg65 q) (meaning1558 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1558 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E158.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112158
