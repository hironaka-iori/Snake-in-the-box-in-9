import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1641 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1641)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 5 6 (meaning1561 q) (meaning1621 q) (meaning1641 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1621 = false ∨ valuation q 1641 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1642 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1642)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 5 7 (meaning1561 q) (meaning1622 q) (meaning1642 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1622 = false ∨ valuation q 1642 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1643 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1643)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 5 8 (meaning1561 q) (meaning1623 q) (meaning1643 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1623 = false ∨ valuation q 1643 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1638 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1638)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 6 2 (meaning1562 q) (meaning1617 q) (meaning1638 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1617 = false ∨ valuation q 1638 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1639 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1639)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 6 3 (meaning1562 q) (meaning1618 q) (meaning1639 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1618 = false ∨ valuation q 1639 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1640 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1640)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 6 4 (meaning1562 q) (meaning1619 q) (meaning1640 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1619 = false ∨ valuation q 1640 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1641 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1641)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 6 5 (meaning1562 q) (meaning1620 q) (meaning1641 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1620 = false ∨ valuation q 1641 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1642 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1642)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 6 6 (meaning1562 q) (meaning1621 q) (meaning1642 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1621 = false ∨ valuation q 1642 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1640 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1640)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 7 3 (meaning1563 q) (meaning1618 q) (meaning1640 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1618 = false ∨ valuation q 1640 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1641 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1641)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 7 4 (meaning1563 q) (meaning1619 q) (meaning1641 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1619 = false ∨ valuation q 1641 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1642 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1642)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 7 5 (meaning1563 q) (meaning1620 q) (meaning1642 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1620 = false ∨ valuation q 1642 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1643 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1643)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 8 5 (meaning1564 q) (meaning1620 q) (meaning1643 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1620 = false ∨ valuation q 1643 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1644 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1644)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 9 5 (meaning1565 q) (meaning1620 q) (meaning1644 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1620 = false ∨ valuation q 1644 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (1652)) (countLit q [-66]) (countLit q [-68]) (count1652 q) 1 (meaningNeg68 q) (meaning1652 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1652 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1652)) (countLit q [-66]) (countLit q [-68]) (count1652 q) 1 (meaningNeg66 q) (meaning1652 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1652 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 68 = true ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-66]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-66)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (1653)) (countLit q [-66]) (countLit q [-68]) (count1652 q) 1 1 (meaningNeg66 q) (meaningNeg68 q) (meaning1653 q) hs
  change (! (valuationOf q 66)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 68 = true ∨ valuation q 1653 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-64]) + (countLit q [-66, -68]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66, -68])
  have hm := merge_right (literal (valuationOf q) (1652)) (literal (valuationOf q) (1654)) (countLit q [-64]) (countLit q [-66, -68]) (count1654 q) 1 (meaning1652 q) (meaning1654 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1654 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1655 = true := by
  have hs : count1654 q = (countLit q [-64]) + (countLit q [-66, -68]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66, -68])
  have hm := merge_right (literal (valuationOf q) (1653)) (literal (valuationOf q) (1655)) (countLit q [-64]) (countLit q [-66, -68]) (count1654 q) 2 (meaning1653 q) (meaning1655 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1655 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-64]) + (countLit q [-66, -68]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66, -68])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1654)) (countLit q [-64]) (countLit q [-66, -68]) (count1654 q) 1 (meaningNeg64 q) (meaning1654 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1654 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1652 = false ∨ valuationOf q 1655 = true := by
  have hs : count1654 q = (countLit q [-64]) + (countLit q [-66, -68]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66, -68])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1655)) (countLit q [-64]) (countLit q [-66, -68]) (count1654 q) 1 1 (meaningNeg64 q) (meaning1652 q) (meaning1655 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1652 = false ∨ valuation q 1655 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1653 = false ∨ valuationOf q 1656 = true := by
  have hs : count1654 q = (countLit q [-64]) + (countLit q [-66, -68]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66, -68])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1656)) (countLit q [-64]) (countLit q [-66, -68]) (count1654 q) 1 2 (meaningNeg64 q) (meaning1653 q) (meaning1656 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1653 = false ∨ valuation q 1656 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-71]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (1657)) (countLit q [-71]) (countLit q [-72]) (count1657 q) 1 (meaningNeg72 q) (meaning1657 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1657 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-71]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1657)) (countLit q [-71]) (countLit q [-72]) (count1657 q) 1 (meaningNeg71 q) (meaning1657 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1657 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 72 = true ∨ valuationOf q 1658 = true := by
  have hs : count1657 q = (countLit q [-71]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-72])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-72)) (literal (valuationOf q) (1658)) (countLit q [-71]) (countLit q [-72]) (count1657 q) 1 1 (meaningNeg71 q) (meaningNeg72 q) (meaning1658 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 72)) = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 72 = true ∨ valuation q 1658 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1659)) (countLit q [-74]) (countLit q [-76]) (count1659 q) 1 (meaningNeg76 q) (meaning1659 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1659 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1659)) (countLit q [-74]) (countLit q [-76]) (count1659 q) 1 (meaningNeg74 q) (meaning1659 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1659 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1660)) (countLit q [-74]) (countLit q [-76]) (count1659 q) 1 1 (meaningNeg74 q) (meaningNeg76 q) (meaning1660 q) hs
  change (! (valuationOf q 74)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 1660 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1661 = true := by
  have hs : count1661 q = (countLit q [-71, -72]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-71, -72]) (l₂ := [-74, -76])
  have hm := merge_right (literal (valuationOf q) (1659)) (literal (valuationOf q) (1661)) (countLit q [-71, -72]) (countLit q [-74, -76]) (count1661 q) 1 (meaning1659 q) (meaning1661 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1661 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1662 = true := by
  have hs : count1661 q = (countLit q [-71, -72]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-71, -72]) (l₂ := [-74, -76])
  have hm := merge_right (literal (valuationOf q) (1660)) (literal (valuationOf q) (1662)) (countLit q [-71, -72]) (countLit q [-74, -76]) (count1661 q) 2 (meaning1660 q) (meaning1662 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1662 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1661 = true := by
  have hs : count1661 q = (countLit q [-71, -72]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-71, -72]) (l₂ := [-74, -76])
  have hm := merge_left (literal (valuationOf q) (1657)) (literal (valuationOf q) (1661)) (countLit q [-71, -72]) (countLit q [-74, -76]) (count1661 q) 1 (meaning1657 q) (meaning1661 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1661 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1662 = true := by
  have hs : count1661 q = (countLit q [-71, -72]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-71, -72]) (l₂ := [-74, -76])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1662)) (countLit q [-71, -72]) (countLit q [-74, -76]) (count1661 q) 1 1 (meaning1657 q) (meaning1659 q) (meaning1662 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1659 = false ∨ valuation q 1662 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1663 = true := by
  have hs : count1661 q = (countLit q [-71, -72]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-71, -72]) (l₂ := [-74, -76])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1663)) (countLit q [-71, -72]) (countLit q [-74, -76]) (count1661 q) 1 2 (meaning1657 q) (meaning1660 q) (meaning1663 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1660 = false ∨ valuation q 1663 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E105.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112105
