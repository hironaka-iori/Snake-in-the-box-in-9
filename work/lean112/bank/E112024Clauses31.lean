import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1555 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1555)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 5 1 (meaning1522 q) (meaning1542 q) (meaning1555 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1542 = false ∨ valuation q 1555 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1556 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1556)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 5 2 (meaning1522 q) (meaning1543 q) (meaning1556 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1543 = false ∨ valuation q 1556 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1557 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1557)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 5 3 (meaning1522 q) (meaning1544 q) (meaning1557 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1544 = false ∨ valuation q 1557 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1558 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1558)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 5 4 (meaning1522 q) (meaning1545 q) (meaning1558 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1545 = false ∨ valuation q 1558 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1556 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1556)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 6 1 (meaning1523 q) (meaning1542 q) (meaning1556 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1542 = false ∨ valuation q 1556 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1575 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1575)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 3 7 (meaning1489 q) (meaning1556 q) (meaning1575 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1556 = false ∨ valuation q 1575 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1573)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 4 4 (meaning1490 q) (meaning1553 q) (meaning1573 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1553 = false ∨ valuation q 1573 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1574 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1574)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 4 5 (meaning1490 q) (meaning1554 q) (meaning1574 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1554 = false ∨ valuation q 1574 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1575 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1575)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 4 6 (meaning1490 q) (meaning1555 q) (meaning1575 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1555 = false ∨ valuation q 1575 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1576 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1576)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 4 7 (meaning1490 q) (meaning1556 q) (meaning1576 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1556 = false ∨ valuation q 1576 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1577 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1577)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 4 8 (meaning1490 q) (meaning1557 q) (meaning1577 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1557 = false ∨ valuation q 1577 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1573)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 5 3 (meaning1491 q) (meaning1552 q) (meaning1573 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1552 = false ∨ valuation q 1573 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1574 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1574)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 5 4 (meaning1491 q) (meaning1553 q) (meaning1574 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1553 = false ∨ valuation q 1574 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1575 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1575)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 5 5 (meaning1491 q) (meaning1554 q) (meaning1575 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1554 = false ∨ valuation q 1575 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1576 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1576)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 5 6 (meaning1491 q) (meaning1555 q) (meaning1576 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1555 = false ∨ valuation q 1576 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1577 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1577)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 5 7 (meaning1491 q) (meaning1556 q) (meaning1577 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1556 = false ∨ valuation q 1577 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1578 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1578)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 5 8 (meaning1491 q) (meaning1557 q) (meaning1578 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1557 = false ∨ valuation q 1578 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1579 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1579)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 5 9 (meaning1491 q) (meaning1558 q) (meaning1579 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1558 = false ∨ valuation q 1579 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1573)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 6 2 (meaning1492 q) (meaning1551 q) (meaning1573 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1551 = false ∨ valuation q 1573 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1574 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1574)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 6 3 (meaning1492 q) (meaning1552 q) (meaning1574 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1552 = false ∨ valuation q 1574 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1575 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1575)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 6 4 (meaning1492 q) (meaning1553 q) (meaning1575 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1553 = false ∨ valuation q 1575 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1576 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1576)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 6 5 (meaning1492 q) (meaning1554 q) (meaning1576 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1554 = false ∨ valuation q 1576 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1577 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1577)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 6 6 (meaning1492 q) (meaning1555 q) (meaning1577 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1555 = false ∨ valuation q 1577 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1578 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1578)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 6 7 (meaning1492 q) (meaning1556 q) (meaning1578 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1556 = false ∨ valuation q 1578 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1579 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1579)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 6 8 (meaning1492 q) (meaning1557 q) (meaning1579 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1557 = false ∨ valuation q 1579 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1580 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1580)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 6 9 (meaning1492 q) (meaning1558 q) (meaning1580 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1558 = false ∨ valuation q 1580 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1574 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1574)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 7 2 (meaning1493 q) (meaning1551 q) (meaning1574 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1551 = false ∨ valuation q 1574 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1575 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1575)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 7 3 (meaning1493 q) (meaning1552 q) (meaning1575 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1552 = false ∨ valuation q 1575 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1576 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1576)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 7 4 (meaning1493 q) (meaning1553 q) (meaning1576 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1553 = false ∨ valuation q 1576 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1577 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1577)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 7 5 (meaning1493 q) (meaning1554 q) (meaning1577 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1554 = false ∨ valuation q 1577 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1578 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1578)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 7 6 (meaning1493 q) (meaning1555 q) (meaning1578 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1555 = false ∨ valuation q 1578 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1579 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1579)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (count1566 q) 7 7 (meaning1493 q) (meaning1556 q) (meaning1579 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1556 = false ∨ valuation q 1579 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E024.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112024
