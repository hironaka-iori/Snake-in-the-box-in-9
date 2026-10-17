import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_left (literal (valuationOf q) (1639)) (literal (valuationOf q) (1643)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1643 q) 1 (meaning1639 q) (meaning1643 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1643 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1644)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1643 q) 1 1 (meaning1639 q) (meaning1641 q) (meaning1644 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = false ∨ valuation q 1644 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1645 = true := by
  have hs : count1643 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1645)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1643 q) 1 2 (meaning1639 q) (meaning1642 q) (meaning1645 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1642 = false ∨ valuation q 1645 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_left (literal (valuationOf q) (1640)) (literal (valuationOf q) (1644)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1643 q) 2 (meaning1640 q) (meaning1644 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1644 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1643 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1643 q) 2 1 (meaning1640 q) (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1641 = false ∨ valuation q 1645 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1646 = true := by
  have hs : count1643 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1646)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1643 q) 2 2 (meaning1640 q) (meaning1642 q) (meaning1646 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1642 = false ∨ valuation q 1646 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1647 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_right (literal (valuationOf q) (1643)) (literal (valuationOf q) (1647)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 1 (meaning1643 q) (meaning1647 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1648 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_right (literal (valuationOf q) (1644)) (literal (valuationOf q) (1648)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 2 (meaning1644 q) (meaning1648 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1648 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1649 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_right (literal (valuationOf q) (1645)) (literal (valuationOf q) (1649)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 3 (meaning1645 q) (meaning1649 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1649 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1647 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1635)) (literal (valuationOf q) (1647)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 1 (meaning1635 q) (meaning1647 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1647 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1648)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 1 1 (meaning1635 q) (meaning1643 q) (meaning1648 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1643 = false ∨ valuation q 1648 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1649)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 1 2 (meaning1635 q) (meaning1644 q) (meaning1649 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1644 = false ∨ valuation q 1649 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1650 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1650)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 1 3 (meaning1635 q) (meaning1645 q) (meaning1650 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1645 = false ∨ valuation q 1650 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1651 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1651)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 1 4 (meaning1635 q) (meaning1646 q) (meaning1651 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1646 = false ∨ valuation q 1651 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1648 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1636)) (literal (valuationOf q) (1648)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 2 (meaning1636 q) (meaning1648 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1648 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1649)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 2 1 (meaning1636 q) (meaning1643 q) (meaning1649 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1643 = false ∨ valuation q 1649 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1650)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 2 2 (meaning1636 q) (meaning1644 q) (meaning1650 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1644 = false ∨ valuation q 1650 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1651 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1651)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 2 3 (meaning1636 q) (meaning1645 q) (meaning1651 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1645 = false ∨ valuation q 1651 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1652 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1652)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 2 4 (meaning1636 q) (meaning1646 q) (meaning1652 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1646 = false ∨ valuation q 1652 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1649 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1637)) (literal (valuationOf q) (1649)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 3 (meaning1637 q) (meaning1649 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1649 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1650)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 3 1 (meaning1637 q) (meaning1643 q) (meaning1650 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1643 = false ∨ valuation q 1650 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1651 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1651)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 3 2 (meaning1637 q) (meaning1644 q) (meaning1651 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1644 = false ∨ valuation q 1651 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1652 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1652)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 3 3 (meaning1637 q) (meaning1645 q) (meaning1652 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1645 = false ∨ valuation q 1652 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1650 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1638)) (literal (valuationOf q) (1650)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 4 (meaning1638 q) (meaning1650 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1650 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1652 = true := by
  have hs : count1647 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1652)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1647 q) 4 2 (meaning1638 q) (meaning1644 q) (meaning1652 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1644 = false ∨ valuation q 1652 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_right (literal (valuationOf q) (1648)) (literal (valuationOf q) (1656)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 2 (meaning1648 q) (meaning1656 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1656 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_right (literal (valuationOf q) (1649)) (literal (valuationOf q) (1657)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 3 (meaning1649 q) (meaning1657 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1657 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1623)) (literal (valuationOf q) (1655)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 1 (meaning1623 q) (meaning1655 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1655 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1656)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 1 1 (meaning1623 q) (meaning1647 q) (meaning1656 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1647 = false ∨ valuation q 1656 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1657)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 1 2 (meaning1623 q) (meaning1648 q) (meaning1657 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1648 = false ∨ valuation q 1657 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1658)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 1 3 (meaning1623 q) (meaning1649 q) (meaning1658 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1649 = false ∨ valuation q 1658 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1659)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 1 4 (meaning1623 q) (meaning1650 q) (meaning1659 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1650 = false ∨ valuation q 1659 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E052.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112052
