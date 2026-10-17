import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-48, -49]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-52, -54])
  have hm := merge_right (literal (valuationOf q) (1595)) (literal (valuationOf q) (1597)) (countLit q [-48, -49]) (countLit q [-52, -54]) (count1596 q) 2 (meaning1595 q) (meaning1597 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1597 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-48, -49]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-52, -54])
  have hm := merge_left (literal (valuationOf q) (1592)) (literal (valuationOf q) (1596)) (countLit q [-48, -49]) (countLit q [-52, -54]) (count1596 q) 1 (meaning1592 q) (meaning1596 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1596 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-48, -49]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-52, -54])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1597)) (countLit q [-48, -49]) (countLit q [-52, -54]) (count1596 q) 1 1 (meaning1592 q) (meaning1594 q) (meaning1597 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1594 = false ∨ valuation q 1597 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1598 = true := by
  have hs : count1596 q = (countLit q [-48, -49]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-52, -54])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1598)) (countLit q [-48, -49]) (countLit q [-52, -54]) (count1596 q) 1 2 (meaning1592 q) (meaning1595 q) (meaning1598 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1595 = false ∨ valuation q 1598 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-48, -49]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-52, -54])
  have hm := merge_left (literal (valuationOf q) (1593)) (literal (valuationOf q) (1597)) (countLit q [-48, -49]) (countLit q [-52, -54]) (count1596 q) 2 (meaning1593 q) (meaning1597 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1597 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1598 = true := by
  have hs : count1596 q = (countLit q [-48, -49]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-52, -54])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1598)) (countLit q [-48, -49]) (countLit q [-52, -54]) (count1596 q) 2 1 (meaning1593 q) (meaning1594 q) (meaning1598 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1594 = false ∨ valuation q 1598 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1599 = true := by
  have hs : count1596 q = (countLit q [-48, -49]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-52, -54])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1599)) (countLit q [-48, -49]) (countLit q [-52, -54]) (count1596 q) 2 2 (meaning1593 q) (meaning1595 q) (meaning1599 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1595 = false ∨ valuation q 1599 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_right (literal (valuationOf q) (-59)) (literal (valuationOf q) (1600)) (countLit q [-56]) (countLit q [-59]) (count1600 q) 1 (meaningNeg59 q) (meaning1600 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1600 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1600)) (countLit q [-56]) (countLit q [-59]) (count1600 q) 1 (meaningNeg56 q) (meaning1600 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1600 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 59 = true ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-59)) (literal (valuationOf q) (1601)) (countLit q [-56]) (countLit q [-59]) (count1600 q) 1 1 (meaningNeg56 q) (meaningNeg59 q) (meaning1601 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 59)) = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 59 = true ∨ valuation q 1601 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-60]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61])
  have hm := merge_right (literal (valuationOf q) (-61)) (literal (valuationOf q) (1602)) (countLit q [-60]) (countLit q [-61]) (count1602 q) 1 (meaningNeg61 q) (meaning1602 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1602 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-60]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1602)) (countLit q [-60]) (countLit q [-61]) (count1602 q) 1 (meaningNeg60 q) (meaning1602 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1602 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 61 = true ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-60]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-61])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (-61)) (literal (valuationOf q) (1603)) (countLit q [-60]) (countLit q [-61]) (count1602 q) 1 1 (meaningNeg60 q) (meaningNeg61 q) (meaning1603 q) hs
  change (! (valuationOf q 60)) = false ∨ (! (valuationOf q 61)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 61 = true ∨ valuation q 1603 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-56, -59]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-56, -59]) (l₂ := [-60, -61])
  have hm := merge_right (literal (valuationOf q) (1602)) (literal (valuationOf q) (1604)) (countLit q [-56, -59]) (countLit q [-60, -61]) (count1604 q) 1 (meaning1602 q) (meaning1604 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1604 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-56, -59]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-56, -59]) (l₂ := [-60, -61])
  have hm := merge_right (literal (valuationOf q) (1603)) (literal (valuationOf q) (1605)) (countLit q [-56, -59]) (countLit q [-60, -61]) (count1604 q) 2 (meaning1603 q) (meaning1605 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1605 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-56, -59]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-56, -59]) (l₂ := [-60, -61])
  have hm := merge_left (literal (valuationOf q) (1600)) (literal (valuationOf q) (1604)) (countLit q [-56, -59]) (countLit q [-60, -61]) (count1604 q) 1 (meaning1600 q) (meaning1604 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1604 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-56, -59]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-56, -59]) (l₂ := [-60, -61])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1605)) (countLit q [-56, -59]) (countLit q [-60, -61]) (count1604 q) 1 1 (meaning1600 q) (meaning1602 q) (meaning1605 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1602 = false ∨ valuation q 1605 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-56, -59]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-56, -59]) (l₂ := [-60, -61])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1606)) (countLit q [-56, -59]) (countLit q [-60, -61]) (count1604 q) 1 2 (meaning1600 q) (meaning1603 q) (meaning1606 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1603 = false ∨ valuation q 1606 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-56, -59]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-56, -59]) (l₂ := [-60, -61])
  have hm := merge_left (literal (valuationOf q) (1601)) (literal (valuationOf q) (1605)) (countLit q [-56, -59]) (countLit q [-60, -61]) (count1604 q) 2 (meaning1601 q) (meaning1605 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1605 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-56, -59]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-56, -59]) (l₂ := [-60, -61])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1606)) (countLit q [-56, -59]) (countLit q [-60, -61]) (count1604 q) 2 1 (meaning1601 q) (meaning1602 q) (meaning1606 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1602 = false ∨ valuation q 1606 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1607 = true := by
  have hs : count1604 q = (countLit q [-56, -59]) + (countLit q [-60, -61]) := List.countP_append (p := literal q) (l₁ := [-56, -59]) (l₂ := [-60, -61])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1607)) (countLit q [-56, -59]) (countLit q [-60, -61]) (count1604 q) 2 2 (meaning1601 q) (meaning1603 q) (meaning1607 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1603 = false ∨ valuation q 1607 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_right (literal (valuationOf q) (1604)) (literal (valuationOf q) (1608)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 1 (meaning1604 q) (meaning1608 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1608 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_right (literal (valuationOf q) (1605)) (literal (valuationOf q) (1609)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 2 (meaning1605 q) (meaning1609 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1609 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1610 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_right (literal (valuationOf q) (1606)) (literal (valuationOf q) (1610)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 3 (meaning1606 q) (meaning1610 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1610 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1611 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_right (literal (valuationOf q) (1607)) (literal (valuationOf q) (1611)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 4 (meaning1607 q) (meaning1611 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1611 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_left (literal (valuationOf q) (1596)) (literal (valuationOf q) (1608)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 1 (meaning1596 q) (meaning1608 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1608 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1609)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 1 1 (meaning1596 q) (meaning1604 q) (meaning1609 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1604 = false ∨ valuation q 1609 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1610 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1610)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 1 2 (meaning1596 q) (meaning1605 q) (meaning1610 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1605 = false ∨ valuation q 1610 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1611 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1611)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 1 3 (meaning1596 q) (meaning1606 q) (meaning1611 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1606 = false ∨ valuation q 1611 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1612 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1612)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 1 4 (meaning1596 q) (meaning1607 q) (meaning1612 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1607 = false ∨ valuation q 1612 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_left (literal (valuationOf q) (1597)) (literal (valuationOf q) (1609)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 2 (meaning1597 q) (meaning1609 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1609 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1610 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1610)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 2 1 (meaning1597 q) (meaning1604 q) (meaning1610 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1604 = false ∨ valuation q 1610 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E105.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112105
