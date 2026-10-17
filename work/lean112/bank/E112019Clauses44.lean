import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1596 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1596)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 6 3 (meaning1520 q) (meaning1575 q) (meaning1596 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1575 = false ∨ valuation q 1596 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1597 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1597)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 6 4 (meaning1520 q) (meaning1576 q) (meaning1597 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1576 = false ∨ valuation q 1597 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1598 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1598)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 6 5 (meaning1520 q) (meaning1577 q) (meaning1598 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1577 = false ∨ valuation q 1598 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1596 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1596)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 7 2 (meaning1521 q) (meaning1574 q) (meaning1596 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1574 = false ∨ valuation q 1596 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1597 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1597)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 7 3 (meaning1521 q) (meaning1575 q) (meaning1597 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1575 = false ∨ valuation q 1597 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1598 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1598)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 7 4 (meaning1521 q) (meaning1576 q) (meaning1598 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1576 = false ∨ valuation q 1598 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1599 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1599)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 7 5 (meaning1521 q) (meaning1577 q) (meaning1599 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1577 = false ∨ valuation q 1599 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1596 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1596)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 8 1 (meaning1522 q) (meaning1573 q) (meaning1596 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1573 = false ∨ valuation q 1596 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1597 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1597)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 8 2 (meaning1522 q) (meaning1574 q) (meaning1597 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1574 = false ∨ valuation q 1597 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1598 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1598)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 8 3 (meaning1522 q) (meaning1575 q) (meaning1598 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1575 = false ∨ valuation q 1598 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1599 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1599)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 8 4 (meaning1522 q) (meaning1576 q) (meaning1599 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1576 = false ∨ valuation q 1599 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1600 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1600)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 8 5 (meaning1522 q) (meaning1577 q) (meaning1600 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1577 = false ∨ valuation q 1600 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1599 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1599)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 9 3 (meaning1523 q) (meaning1575 q) (meaning1599 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1575 = false ∨ valuation q 1599 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1607 = true := by
  have hs : count1607 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1607)) (countLit q [-64]) (countLit q [-66]) (count1607 q) 1 (meaningNeg66 q) (meaning1607 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1607 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1607 = true := by
  have hs : count1607 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1607)) (countLit q [-64]) (countLit q [-66]) (count1607 q) 1 (meaningNeg64 q) (meaning1607 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1607 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1608 = true := by
  have hs : count1607 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1608)) (countLit q [-64]) (countLit q [-66]) (count1607 q) 1 1 (meaningNeg64 q) (meaningNeg66 q) (meaning1608 q) hs
  change (! (valuationOf q 64)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 1608 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1609 = true := by
  have hs : count1609 q = (countLit q [-63]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -66])
  have hm := merge_right (literal (valuationOf q) (1607)) (literal (valuationOf q) (1609)) (countLit q [-63]) (countLit q [-64, -66]) (count1609 q) 1 (meaning1607 q) (meaning1609 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1609 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1610 = true := by
  have hs : count1609 q = (countLit q [-63]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -66])
  have hm := merge_right (literal (valuationOf q) (1608)) (literal (valuationOf q) (1610)) (countLit q [-63]) (countLit q [-64, -66]) (count1609 q) 2 (meaning1608 q) (meaning1610 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1610 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1609 = true := by
  have hs : count1609 q = (countLit q [-63]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1609)) (countLit q [-63]) (countLit q [-64, -66]) (count1609 q) 1 (meaningNeg63 q) (meaning1609 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1609 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1607 = false ∨ valuationOf q 1610 = true := by
  have hs : count1609 q = (countLit q [-63]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -66])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1610)) (countLit q [-63]) (countLit q [-64, -66]) (count1609 q) 1 1 (meaningNeg63 q) (meaning1607 q) (meaning1610 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1607 = false ∨ valuation q 1610 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1608 = false ∨ valuationOf q 1611 = true := by
  have hs : count1609 q = (countLit q [-63]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -66])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1611)) (countLit q [-63]) (countLit q [-64, -66]) (count1609 q) 1 2 (meaningNeg63 q) (meaning1608 q) (meaning1611 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1608 = false ∨ valuation q 1611 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (1612)) (countLit q [-67]) (countLit q [-69]) (count1612 q) 1 (meaningNeg69 q) (meaning1612 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1612 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1612)) (countLit q [-67]) (countLit q [-69]) (count1612 q) 1 (meaningNeg67 q) (meaning1612 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1612 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 69 = true ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-67]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-69)) (literal (valuationOf q) (1613)) (countLit q [-67]) (countLit q [-69]) (count1612 q) 1 1 (meaningNeg67 q) (meaningNeg69 q) (meaning1613 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 69)) = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 69 = true ∨ valuation q 1613 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1614 = true := by
  have hs : count1614 q = (countLit q [-71]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (1614)) (countLit q [-71]) (countLit q [-72]) (count1614 q) 1 (meaningNeg72 q) (meaning1614 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1614 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1614 = true := by
  have hs : count1614 q = (countLit q [-71]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1614)) (countLit q [-71]) (countLit q [-72]) (count1614 q) 1 (meaningNeg71 q) (meaning1614 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1614 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 72 = true ∨ valuationOf q 1615 = true := by
  have hs : count1614 q = (countLit q [-71]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-72)) (literal (valuationOf q) (1615)) (countLit q [-71]) (countLit q [-72]) (count1614 q) 1 1 (meaningNeg71 q) (meaningNeg72 q) (meaning1615 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 72)) = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 72 = true ∨ valuation q 1615 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-67, -69]) + (countLit q [-71, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-71, -72])
  have hm := merge_right (literal (valuationOf q) (1614)) (literal (valuationOf q) (1616)) (countLit q [-67, -69]) (countLit q [-71, -72]) (count1616 q) 1 (meaning1614 q) (meaning1616 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1616 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-67, -69]) + (countLit q [-71, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-71, -72])
  have hm := merge_right (literal (valuationOf q) (1615)) (literal (valuationOf q) (1617)) (countLit q [-67, -69]) (countLit q [-71, -72]) (count1616 q) 2 (meaning1615 q) (meaning1617 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1617 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-67, -69]) + (countLit q [-71, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-71, -72])
  have hm := merge_left (literal (valuationOf q) (1612)) (literal (valuationOf q) (1616)) (countLit q [-67, -69]) (countLit q [-71, -72]) (count1616 q) 1 (meaning1612 q) (meaning1616 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1616 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-67, -69]) + (countLit q [-71, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-71, -72])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1617)) (countLit q [-67, -69]) (countLit q [-71, -72]) (count1616 q) 1 1 (meaning1612 q) (meaning1614 q) (meaning1617 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1614 = false ∨ valuation q 1617 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-67, -69]) + (countLit q [-71, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-71, -72])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1618)) (countLit q [-67, -69]) (countLit q [-71, -72]) (count1616 q) 1 2 (meaning1612 q) (meaning1615 q) (meaning1618 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1615 = false ∨ valuation q 1618 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E019.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112019
