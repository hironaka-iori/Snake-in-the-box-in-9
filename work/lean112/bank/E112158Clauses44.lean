import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-89, -92, -93]) + (countLit q [-95, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93]) (l₂ := [-95, -98, -100, -102])
  have hm := merge_left (literal (valuationOf q) (1615)) (literal (valuationOf q) (1626)) (countLit q [-89, -92, -93]) (countLit q [-95, -98, -100, -102]) (count1625 q) 2 (meaning1615 q) (meaning1626 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1626 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1627 = true := by
  have hs : count1625 q = (countLit q [-89, -92, -93]) + (countLit q [-95, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93]) (l₂ := [-95, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1627)) (countLit q [-89, -92, -93]) (countLit q [-95, -98, -100, -102]) (count1625 q) 2 1 (meaning1615 q) (meaning1621 q) (meaning1627 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1621 = false ∨ valuation q 1627 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1628 = true := by
  have hs : count1625 q = (countLit q [-89, -92, -93]) + (countLit q [-95, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93]) (l₂ := [-95, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1628)) (countLit q [-89, -92, -93]) (countLit q [-95, -98, -100, -102]) (count1625 q) 2 2 (meaning1615 q) (meaning1622 q) (meaning1628 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1622 = false ∨ valuation q 1628 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1627 = true := by
  have hs : count1625 q = (countLit q [-89, -92, -93]) + (countLit q [-95, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93]) (l₂ := [-95, -98, -100, -102])
  have hm := merge_left (literal (valuationOf q) (1616)) (literal (valuationOf q) (1627)) (countLit q [-89, -92, -93]) (countLit q [-95, -98, -100, -102]) (count1625 q) 3 (meaning1616 q) (meaning1627 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1627 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1628 = true := by
  have hs : count1625 q = (countLit q [-89, -92, -93]) + (countLit q [-95, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93]) (l₂ := [-95, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1628)) (countLit q [-89, -92, -93]) (countLit q [-95, -98, -100, -102]) (count1625 q) 3 1 (meaning1616 q) (meaning1621 q) (meaning1628 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1621 = false ∨ valuation q 1628 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1629 = true := by
  have hs : count1625 q = (countLit q [-89, -92, -93]) + (countLit q [-95, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93]) (l₂ := [-95, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1629)) (countLit q [-89, -92, -93]) (countLit q [-95, -98, -100, -102]) (count1625 q) 3 2 (meaning1616 q) (meaning1622 q) (meaning1629 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1622 = false ∨ valuation q 1629 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1632)) (countLit q [-104]) (countLit q [-107]) (count1632 q) 1 (meaningNeg107 q) (meaning1632 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1632 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1632)) (countLit q [-104]) (countLit q [-107]) (count1632 q) 1 (meaningNeg104 q) (meaning1632 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1632 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 107 = true ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-104]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-107])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-107)) (literal (valuationOf q) (1633)) (countLit q [-104]) (countLit q [-107]) (count1632 q) 1 1 (meaningNeg104 q) (meaningNeg107 q) (meaning1633 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 107)) = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 107 = true ∨ valuation q 1633 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_right (literal (valuationOf q) (-110)) (literal (valuationOf q) (1634)) (countLit q [-109]) (countLit q [-110]) (count1634 q) 1 (meaningNeg110 q) (meaning1634 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1634 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-109)) (literal (valuationOf q) (1634)) (countLit q [-109]) (countLit q [-110]) (count1634 q) 1 (meaningNeg109 q) (meaning1634 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1634 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 110 = true ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_two (literal (valuationOf q) (-109)) (literal (valuationOf q) (-110)) (literal (valuationOf q) (1635)) (countLit q [-109]) (countLit q [-110]) (count1634 q) 1 1 (meaningNeg109 q) (meaningNeg110 q) (meaning1635 q) hs
  change (! (valuationOf q 109)) = false ∨ (! (valuationOf q 110)) = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 110 = true ∨ valuation q 1635 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1636 = true := by
  have hs : count1636 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_right (literal (valuationOf q) (1634)) (literal (valuationOf q) (1636)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1636 q) 1 (meaning1634 q) (meaning1636 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1636 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1637 = true := by
  have hs : count1636 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_right (literal (valuationOf q) (1635)) (literal (valuationOf q) (1637)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1636 q) 2 (meaning1635 q) (meaning1637 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1637 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1636 = true := by
  have hs : count1636 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_left (literal (valuationOf q) (1632)) (literal (valuationOf q) (1636)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1636 q) 1 (meaning1632 q) (meaning1636 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1636 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1637 = true := by
  have hs : count1636 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1637)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1636 q) 1 1 (meaning1632 q) (meaning1634 q) (meaning1637 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1634 = false ∨ valuation q 1637 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1635 = false ∨ valuationOf q 1638 = true := by
  have hs : count1636 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1635)) (literal (valuationOf q) (1638)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1636 q) 1 2 (meaning1632 q) (meaning1635 q) (meaning1638 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1635 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1635 = false ∨ valuation q 1638 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1637 = true := by
  have hs : count1636 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_left (literal (valuationOf q) (1633)) (literal (valuationOf q) (1637)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1636 q) 2 (meaning1633 q) (meaning1637 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1637 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1638 = true := by
  have hs : count1636 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_two (literal (valuationOf q) (1633)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1638)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1636 q) 2 1 (meaning1633 q) (meaning1634 q) (meaning1638 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1634 = false ∨ valuation q 1638 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1635 = false ∨ valuationOf q 1639 = true := by
  have hs : count1636 q = (countLit q [-104, -107]) + (countLit q [-109, -110]) := List.countP_append (p := literal q) (l₁ := [-104, -107]) (l₂ := [-109, -110])
  have hm := merge_two (literal (valuationOf q) (1633)) (literal (valuationOf q) (1635)) (literal (valuationOf q) (1639)) (countLit q [-104, -107]) (countLit q [-109, -110]) (count1636 q) 2 2 (meaning1633 q) (meaning1635 q) (meaning1639 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1635 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1635 = false ∨ valuation q 1639 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1640 = true := by
  have hs : count1640 q = (countLit q [-111]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-114])
  have hm := merge_right (literal (valuationOf q) (-114)) (literal (valuationOf q) (1640)) (countLit q [-111]) (countLit q [-114]) (count1640 q) 1 (meaningNeg114 q) (meaning1640 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1640 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1640 = true := by
  have hs : count1640 q = (countLit q [-111]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-114])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1640)) (countLit q [-111]) (countLit q [-114]) (count1640 q) 1 (meaningNeg111 q) (meaning1640 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1640 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 114 = true ∨ valuationOf q 1641 = true := by
  have hs : count1640 q = (countLit q [-111]) + (countLit q [-114]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-114])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-114)) (literal (valuationOf q) (1641)) (countLit q [-111]) (countLit q [-114]) (count1640 q) 1 1 (meaningNeg111 q) (meaningNeg114 q) (meaning1641 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 114)) = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 114 = true ∨ valuation q 1641 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1642 = true := by
  have hs : count1642 q = (countLit q [-117]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-118])
  have hm := merge_right (literal (valuationOf q) (-118)) (literal (valuationOf q) (1642)) (countLit q [-117]) (countLit q [-118]) (count1642 q) 1 (meaningNeg118 q) (meaning1642 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1642 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1642 = true := by
  have hs : count1642 q = (countLit q [-117]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-118])
  have hm := merge_left (literal (valuationOf q) (-117)) (literal (valuationOf q) (1642)) (countLit q [-117]) (countLit q [-118]) (count1642 q) 1 (meaningNeg117 q) (meaning1642 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1642 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 118 = true ∨ valuationOf q 1643 = true := by
  have hs : count1642 q = (countLit q [-117]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-118])
  have hm := merge_two (literal (valuationOf q) (-117)) (literal (valuationOf q) (-118)) (literal (valuationOf q) (1643)) (countLit q [-117]) (countLit q [-118]) (count1642 q) 1 1 (meaningNeg117 q) (meaningNeg118 q) (meaning1643 q) hs
  change (! (valuationOf q 117)) = false ∨ (! (valuationOf q 118)) = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 118 = true ∨ valuation q 1643 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1644 = true := by
  have hs : count1644 q = (countLit q [-111, -114]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-117, -118])
  have hm := merge_right (literal (valuationOf q) (1642)) (literal (valuationOf q) (1644)) (countLit q [-111, -114]) (countLit q [-117, -118]) (count1644 q) 1 (meaning1642 q) (meaning1644 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1644 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1645 = true := by
  have hs : count1644 q = (countLit q [-111, -114]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-117, -118])
  have hm := merge_right (literal (valuationOf q) (1643)) (literal (valuationOf q) (1645)) (countLit q [-111, -114]) (countLit q [-117, -118]) (count1644 q) 2 (meaning1643 q) (meaning1645 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1645 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1644 = true := by
  have hs : count1644 q = (countLit q [-111, -114]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-117, -118])
  have hm := merge_left (literal (valuationOf q) (1640)) (literal (valuationOf q) (1644)) (countLit q [-111, -114]) (countLit q [-117, -118]) (count1644 q) 1 (meaning1640 q) (meaning1644 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1644 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1645 = true := by
  have hs : count1644 q = (countLit q [-111, -114]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-117, -118])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1645)) (countLit q [-111, -114]) (countLit q [-117, -118]) (count1644 q) 1 1 (meaning1640 q) (meaning1642 q) (meaning1645 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1642 = false ∨ valuation q 1645 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1646 = true := by
  have hs : count1644 q = (countLit q [-111, -114]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-117, -118])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1646)) (countLit q [-111, -114]) (countLit q [-117, -118]) (count1644 q) 1 2 (meaning1640 q) (meaning1643 q) (meaning1646 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1643 = false ∨ valuation q 1646 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1644 q = (countLit q [-111, -114]) + (countLit q [-117, -118]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-117, -118])
  have hm := merge_left (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-111, -114]) (countLit q [-117, -118]) (count1644 q) 2 (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1645 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E158.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112158
