import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1625)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 2 1 (meaning1612 q) (meaning1619 q) (meaning1625 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1619 = false ∨ valuation q 1625 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1626)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 2 2 (meaning1612 q) (meaning1620 q) (meaning1626 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1620 = false ∨ valuation q 1626 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1627 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1627)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 2 3 (meaning1612 q) (meaning1621 q) (meaning1627 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1621 = false ∨ valuation q 1627 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_left (literal (valuationOf q) (1613)) (literal (valuationOf q) (1625)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 3 (meaning1613 q) (meaning1625 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1625 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1626)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 3 1 (meaning1613 q) (meaning1619 q) (meaning1626 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1619 = false ∨ valuation q 1626 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1627 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1627)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 3 2 (meaning1613 q) (meaning1620 q) (meaning1627 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1620 = false ∨ valuation q 1627 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1628 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1628)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 3 3 (meaning1613 q) (meaning1621 q) (meaning1628 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1621 = false ∨ valuation q 1628 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_left (literal (valuationOf q) (1614)) (literal (valuationOf q) (1626)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 4 (meaning1614 q) (meaning1626 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1626 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1627 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1627)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 4 1 (meaning1614 q) (meaning1619 q) (meaning1627 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1619 = false ∨ valuation q 1627 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1628 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1628)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 4 2 (meaning1614 q) (meaning1620 q) (meaning1628 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1620 = false ∨ valuation q 1628 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1631 = true := by
  have hs : count1631 q = (countLit q [-46]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1631)) (countLit q [-46]) (countLit q [-51]) (count1631 q) 1 (meaningNeg51 q) (meaning1631 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1631 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1631 = true := by
  have hs : count1631 q = (countLit q [-46]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1631)) (countLit q [-46]) (countLit q [-51]) (count1631 q) 1 (meaningNeg46 q) (meaning1631 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1631 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1632 = true := by
  have hs : count1631 q = (countLit q [-46]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1632)) (countLit q [-46]) (countLit q [-51]) (count1631 q) 1 1 (meaningNeg46 q) (meaningNeg51 q) (meaning1632 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 51 = true ∨ valuation q 1632 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1633 = true := by
  have hs : count1633 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1633)) (countLit q [-53]) (countLit q [-54]) (count1633 q) 1 (meaningNeg54 q) (meaning1633 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1633 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1633 = true := by
  have hs : count1633 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1633)) (countLit q [-53]) (countLit q [-54]) (count1633 q) 1 (meaningNeg53 q) (meaning1633 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1633 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1634 = true := by
  have hs : count1633 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1634)) (countLit q [-53]) (countLit q [-54]) (count1633 q) 1 1 (meaningNeg53 q) (meaningNeg54 q) (meaning1634 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 54 = true ∨ valuation q 1634 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1635 = true := by
  have hs : count1635 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1635)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1635 q) 1 (meaning1633 q) (meaning1635 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1635 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1636 = true := by
  have hs : count1635 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_right (literal (valuationOf q) (1634)) (literal (valuationOf q) (1636)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1635 q) 2 (meaning1634 q) (meaning1636 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1636 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1635 = true := by
  have hs : count1635 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_left (literal (valuationOf q) (1631)) (literal (valuationOf q) (1635)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1635 q) 1 (meaning1631 q) (meaning1635 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1635 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true := by
  have hs : count1635 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1636)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1635 q) 1 1 (meaning1631 q) (meaning1633 q) (meaning1636 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1633 = false ∨ valuation q 1636 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1637 = true := by
  have hs : count1635 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1637)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1635 q) 1 2 (meaning1631 q) (meaning1634 q) (meaning1637 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1634 = false ∨ valuation q 1637 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1636 = true := by
  have hs : count1635 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_left (literal (valuationOf q) (1632)) (literal (valuationOf q) (1636)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1635 q) 2 (meaning1632 q) (meaning1636 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1636 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1637 = true := by
  have hs : count1635 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1637)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1635 q) 2 1 (meaning1632 q) (meaning1633 q) (meaning1637 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1633 = false ∨ valuation q 1637 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1638 = true := by
  have hs : count1635 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1638)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1635 q) 2 2 (meaning1632 q) (meaning1634 q) (meaning1638 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1634 = false ∨ valuation q 1638 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-56]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (1639)) (countLit q [-56]) (countLit q [-60]) (count1639 q) 1 (meaningNeg60 q) (meaning1639 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1639 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-56]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1639)) (countLit q [-56]) (countLit q [-60]) (count1639 q) 1 (meaningNeg56 q) (meaning1639 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1639 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 60 = true ∨ valuationOf q 1640 = true := by
  have hs : count1639 q = (countLit q [-56]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-60])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-60)) (literal (valuationOf q) (1640)) (countLit q [-56]) (countLit q [-60]) (count1639 q) 1 1 (meaningNeg56 q) (meaningNeg60 q) (meaning1640 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 60)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 60 = true ∨ valuation q 1640 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1641)) (countLit q [-62]) (countLit q [-63]) (count1641 q) 1 (meaningNeg63 q) (meaning1641 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1641 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (1641)) (countLit q [-62]) (countLit q [-63]) (count1641 q) 1 (meaningNeg62 q) (meaning1641 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1641 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1642)) (countLit q [-62]) (countLit q [-63]) (count1641 q) 1 1 (meaningNeg62 q) (meaningNeg63 q) (meaning1642 q) hs
  change (! (valuationOf q 62)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 63 = true ∨ valuation q 1642 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_right (literal (valuationOf q) (1641)) (literal (valuationOf q) (1643)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1643 q) 1 (meaning1641 q) (meaning1643 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1643 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_right (literal (valuationOf q) (1642)) (literal (valuationOf q) (1644)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1643 q) 2 (meaning1642 q) (meaning1644 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1644 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E052.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112052
