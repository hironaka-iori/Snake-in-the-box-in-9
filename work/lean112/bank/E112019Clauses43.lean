import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1577 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_left (literal (valuationOf q) (1546)) (literal (valuationOf q) (1577)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 5 (meaning1546 q) (meaning1577 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1577 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1579 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1579)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 5 2 (meaning1546 q) (meaning1566 q) (meaning1579 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1566 = false ∨ valuation q 1579 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1580 = true := by
  have hs : count1573 q = (countLit q [-33, -35, -36, -38, -41, -43, -44]) + (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -36, -38, -41, -43, -44]) (l₂ := [-46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1580)) (countLit q [-33, -35, -36, -38, -41, -43, -44]) (countLit q [-46, -48, -51, -52, -54, -55, -58, -61]) (count1573 q) 5 3 (meaning1546 q) (meaning1567 q) (meaning1580 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1567 = false ∨ valuation q 1580 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1593 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1593)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 1 5 (meaning1515 q) (meaning1577 q) (meaning1593 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1577 = false ∨ valuation q 1593 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1591 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1591)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 2 2 (meaning1516 q) (meaning1574 q) (meaning1591 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1574 = false ∨ valuation q 1591 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1592 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1592)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 2 3 (meaning1516 q) (meaning1575 q) (meaning1592 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1575 = false ∨ valuation q 1592 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1593 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1593)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 2 4 (meaning1516 q) (meaning1576 q) (meaning1593 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1576 = false ∨ valuation q 1593 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1594 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1594)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 2 5 (meaning1516 q) (meaning1577 q) (meaning1594 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1577 = false ∨ valuation q 1594 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1595 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1595)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 2 6 (meaning1516 q) (meaning1578 q) (meaning1595 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1578 = false ∨ valuation q 1595 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1596 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1596)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 2 7 (meaning1516 q) (meaning1579 q) (meaning1596 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1579 = false ∨ valuation q 1596 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1591 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1591)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 3 1 (meaning1517 q) (meaning1573 q) (meaning1591 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1573 = false ∨ valuation q 1591 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1592 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1592)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 3 2 (meaning1517 q) (meaning1574 q) (meaning1592 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1574 = false ∨ valuation q 1592 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1593 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1593)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 3 3 (meaning1517 q) (meaning1575 q) (meaning1593 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1575 = false ∨ valuation q 1593 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1594 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1594)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 3 4 (meaning1517 q) (meaning1576 q) (meaning1594 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1576 = false ∨ valuation q 1594 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1595 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1595)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 3 5 (meaning1517 q) (meaning1577 q) (meaning1595 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1577 = false ∨ valuation q 1595 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1596 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1596)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 3 6 (meaning1517 q) (meaning1578 q) (meaning1596 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1578 = false ∨ valuation q 1596 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1597 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1597)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 3 7 (meaning1517 q) (meaning1579 q) (meaning1597 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1579 = false ∨ valuation q 1597 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1598 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1598)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 3 8 (meaning1517 q) (meaning1580 q) (meaning1598 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1580 = false ∨ valuation q 1598 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1592 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1592)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 4 1 (meaning1518 q) (meaning1573 q) (meaning1592 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1573 = false ∨ valuation q 1592 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1593 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1593)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 4 2 (meaning1518 q) (meaning1574 q) (meaning1593 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1574 = false ∨ valuation q 1593 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1594 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1594)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 4 3 (meaning1518 q) (meaning1575 q) (meaning1594 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1575 = false ∨ valuation q 1594 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1595 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1595)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 4 4 (meaning1518 q) (meaning1576 q) (meaning1595 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1576 = false ∨ valuation q 1595 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1596 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1596)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 4 5 (meaning1518 q) (meaning1577 q) (meaning1596 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1577 = false ∨ valuation q 1596 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1597 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1597)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 4 6 (meaning1518 q) (meaning1578 q) (meaning1597 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1578 = false ∨ valuation q 1597 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1593 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1593)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 5 1 (meaning1519 q) (meaning1573 q) (meaning1593 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1573 = false ∨ valuation q 1593 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1594 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1594)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 5 2 (meaning1519 q) (meaning1574 q) (meaning1594 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1574 = false ∨ valuation q 1594 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1595 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1595)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 5 3 (meaning1519 q) (meaning1575 q) (meaning1595 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1575 = false ∨ valuation q 1595 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1596 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1596)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 5 4 (meaning1519 q) (meaning1576 q) (meaning1596 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1576 = false ∨ valuation q 1596 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1597 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1597)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 5 5 (meaning1519 q) (meaning1577 q) (meaning1597 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1577 = false ∨ valuation q 1597 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1598 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1598)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 5 6 (meaning1519 q) (meaning1578 q) (meaning1598 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1578 = false ∨ valuation q 1598 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1594 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1594)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 6 1 (meaning1520 q) (meaning1573 q) (meaning1594 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1573 = false ∨ valuation q 1594 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1595 = true := by
  have hs : count1588 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) + (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (l₂ := [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1595)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]) (countLit q [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (count1588 q) 6 2 (meaning1520 q) (meaning1574 q) (meaning1595 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1574 = false ∨ valuation q 1595 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E019.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112019
