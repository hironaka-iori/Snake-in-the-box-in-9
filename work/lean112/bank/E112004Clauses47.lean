import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-90, -91]) + (countLit q [-97, -98]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-97, -98])
  have hm := merge_left (literal (valuationOf q) (1639)) (literal (valuationOf q) (1643)) (countLit q [-90, -91]) (countLit q [-97, -98]) (count1643 q) 1 (meaning1639 q) (meaning1643 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1643 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-90, -91]) + (countLit q [-97, -98]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-97, -98])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1644)) (countLit q [-90, -91]) (countLit q [-97, -98]) (count1643 q) 1 1 (meaning1639 q) (meaning1641 q) (meaning1644 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = false ∨ valuation q 1644 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1645 = true := by
  have hs : count1643 q = (countLit q [-90, -91]) + (countLit q [-97, -98]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-97, -98])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1645)) (countLit q [-90, -91]) (countLit q [-97, -98]) (count1643 q) 1 2 (meaning1639 q) (meaning1642 q) (meaning1645 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1642 = false ∨ valuation q 1645 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-90, -91]) + (countLit q [-97, -98]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-97, -98])
  have hm := merge_left (literal (valuationOf q) (1640)) (literal (valuationOf q) (1644)) (countLit q [-90, -91]) (countLit q [-97, -98]) (count1643 q) 2 (meaning1640 q) (meaning1644 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1644 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1643 q = (countLit q [-90, -91]) + (countLit q [-97, -98]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-97, -98])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-90, -91]) (countLit q [-97, -98]) (count1643 q) 2 1 (meaning1640 q) (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1641 = false ∨ valuation q 1645 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1646 = true := by
  have hs : count1643 q = (countLit q [-90, -91]) + (countLit q [-97, -98]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-97, -98])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1646)) (countLit q [-90, -91]) (countLit q [-97, -98]) (count1643 q) 2 2 (meaning1640 q) (meaning1642 q) (meaning1646 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1642 = false ∨ valuation q 1646 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1647 = true := by
  have hs : count1647 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1647)) (countLit q [-101]) (countLit q [-102]) (count1647 q) 1 (meaningNeg102 q) (meaning1647 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1647 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1647 = true := by
  have hs : count1647 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1647)) (countLit q [-101]) (countLit q [-102]) (count1647 q) 1 (meaningNeg101 q) (meaning1647 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1647 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 102 = true ∨ valuationOf q 1648 = true := by
  have hs : count1647 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_two (literal (valuationOf q) (-101)) (literal (valuationOf q) (-102)) (literal (valuationOf q) (1648)) (countLit q [-101]) (countLit q [-102]) (count1647 q) 1 1 (meaningNeg101 q) (meaningNeg102 q) (meaning1648 q) hs
  change (! (valuationOf q 101)) = false ∨ (! (valuationOf q 102)) = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 102 = true ∨ valuation q 1648 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1649 = true := by
  have hs : count1649 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1649)) (countLit q [-103]) (countLit q [-105]) (count1649 q) 1 (meaningNeg105 q) (meaning1649 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1649 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1649 = true := by
  have hs : count1649 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1649)) (countLit q [-103]) (countLit q [-105]) (count1649 q) 1 (meaningNeg103 q) (meaning1649 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1649 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1650 = true := by
  have hs : count1649 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1650)) (countLit q [-103]) (countLit q [-105]) (count1649 q) 1 1 (meaningNeg103 q) (meaningNeg105 q) (meaning1650 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 1650 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1651 = true := by
  have hs : count1651 q = (countLit q [-101, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-103, -105])
  have hm := merge_right (literal (valuationOf q) (1649)) (literal (valuationOf q) (1651)) (countLit q [-101, -102]) (countLit q [-103, -105]) (count1651 q) 1 (meaning1649 q) (meaning1651 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1651 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1652 = true := by
  have hs : count1651 q = (countLit q [-101, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-103, -105])
  have hm := merge_right (literal (valuationOf q) (1650)) (literal (valuationOf q) (1652)) (countLit q [-101, -102]) (countLit q [-103, -105]) (count1651 q) 2 (meaning1650 q) (meaning1652 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1652 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1651 = true := by
  have hs : count1651 q = (countLit q [-101, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-103, -105])
  have hm := merge_left (literal (valuationOf q) (1647)) (literal (valuationOf q) (1651)) (countLit q [-101, -102]) (countLit q [-103, -105]) (count1651 q) 1 (meaning1647 q) (meaning1651 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1651 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1652 = true := by
  have hs : count1651 q = (countLit q [-101, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-103, -105])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1652)) (countLit q [-101, -102]) (countLit q [-103, -105]) (count1651 q) 1 1 (meaning1647 q) (meaning1649 q) (meaning1652 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1649 = false ∨ valuation q 1652 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1653 = true := by
  have hs : count1651 q = (countLit q [-101, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-103, -105])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1653)) (countLit q [-101, -102]) (countLit q [-103, -105]) (count1651 q) 1 2 (meaning1647 q) (meaning1650 q) (meaning1653 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1650 = false ∨ valuation q 1653 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1652 = true := by
  have hs : count1651 q = (countLit q [-101, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-103, -105])
  have hm := merge_left (literal (valuationOf q) (1648)) (literal (valuationOf q) (1652)) (countLit q [-101, -102]) (countLit q [-103, -105]) (count1651 q) 2 (meaning1648 q) (meaning1652 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1652 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1653 = true := by
  have hs : count1651 q = (countLit q [-101, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-103, -105])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1653)) (countLit q [-101, -102]) (countLit q [-103, -105]) (count1651 q) 2 1 (meaning1648 q) (meaning1649 q) (meaning1653 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1649 = false ∨ valuation q 1653 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1654 = true := by
  have hs : count1651 q = (countLit q [-101, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-103, -105])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1654)) (countLit q [-101, -102]) (countLit q [-103, -105]) (count1651 q) 2 2 (meaning1648 q) (meaning1650 q) (meaning1654 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1650 = false ∨ valuation q 1654 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1651)) (literal (valuationOf q) (1655)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 1 (meaning1651 q) (meaning1655 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1655 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1652)) (literal (valuationOf q) (1656)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 2 (meaning1652 q) (meaning1656 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1656 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1653)) (literal (valuationOf q) (1657)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 3 (meaning1653 q) (meaning1657 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1657 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1654)) (literal (valuationOf q) (1658)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 4 (meaning1654 q) (meaning1658 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1658 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1643)) (literal (valuationOf q) (1655)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 1 (meaning1643 q) (meaning1655 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1655 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1656)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 1 1 (meaning1643 q) (meaning1651 q) (meaning1656 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1651 = false ∨ valuation q 1656 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1657)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 1 2 (meaning1643 q) (meaning1652 q) (meaning1657 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1652 = false ∨ valuation q 1657 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1658)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 1 3 (meaning1643 q) (meaning1653 q) (meaning1658 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1653 = false ∨ valuation q 1658 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1659)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 1 4 (meaning1643 q) (meaning1654 q) (meaning1659 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1654 = false ∨ valuation q 1659 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1644)) (literal (valuationOf q) (1656)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 2 (meaning1644 q) (meaning1656 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1656 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1657)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 2 1 (meaning1644 q) (meaning1651 q) (meaning1657 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1651 = false ∨ valuation q 1657 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1658)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 2 2 (meaning1644 q) (meaning1652 q) (meaning1658 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1652 = false ∨ valuation q 1658 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E004.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112004
