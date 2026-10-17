import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1670 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_right (literal (valuationOf q) (1666)) (literal (valuationOf q) (1670)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 1 (meaning1666 q) (meaning1670 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1670 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1671 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_right (literal (valuationOf q) (1667)) (literal (valuationOf q) (1671)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 2 (meaning1667 q) (meaning1671 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1671 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1672 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_right (literal (valuationOf q) (1668)) (literal (valuationOf q) (1672)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 3 (meaning1668 q) (meaning1672 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1672 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1670 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_left (literal (valuationOf q) (1658)) (literal (valuationOf q) (1670)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 1 (meaning1658 q) (meaning1670 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1670 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1671 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1671)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 1 1 (meaning1658 q) (meaning1666 q) (meaning1671 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1666 = false ∨ valuation q 1671 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1672 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1672)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 1 2 (meaning1658 q) (meaning1667 q) (meaning1672 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1667 = false ∨ valuation q 1672 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1673 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1673)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 1 3 (meaning1658 q) (meaning1668 q) (meaning1673 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1668 = false ∨ valuation q 1673 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1671 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_left (literal (valuationOf q) (1659)) (literal (valuationOf q) (1671)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 2 (meaning1659 q) (meaning1671 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1671 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1672 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1672)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 2 1 (meaning1659 q) (meaning1666 q) (meaning1672 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1666 = false ∨ valuation q 1672 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1673 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1673)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 2 2 (meaning1659 q) (meaning1667 q) (meaning1673 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1667 = false ∨ valuation q 1673 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1674 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1674)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 2 3 (meaning1659 q) (meaning1668 q) (meaning1674 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1668 = false ∨ valuation q 1674 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1672 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_left (literal (valuationOf q) (1660)) (literal (valuationOf q) (1672)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 3 (meaning1660 q) (meaning1672 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1672 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1673 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1673)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 3 1 (meaning1660 q) (meaning1666 q) (meaning1673 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1666 = false ∨ valuation q 1673 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1674 = true := by
  have hs : count1670 q = (countLit q [-45, -49, -52, -53]) + (countLit q [-55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-45, -49, -52, -53]) (l₂ := [-55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1674)) (countLit q [-45, -49, -52, -53]) (countLit q [-55, -57, -58, -62]) (count1670 q) 3 2 (meaning1660 q) (meaning1667 q) (meaning1674 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1667 = false ∨ valuation q 1674 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1680 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1680)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 1 2 (meaning1646 q) (meaning1671 q) (meaning1680 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1671 = false ∨ valuation q 1680 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1681 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1681)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 1 3 (meaning1646 q) (meaning1672 q) (meaning1681 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1672 = false ∨ valuation q 1681 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1682 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1682)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 1 4 (meaning1646 q) (meaning1673 q) (meaning1682 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1673 = false ∨ valuation q 1682 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1683 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1674)) (literal (valuationOf q) (1683)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 1 5 (meaning1646 q) (meaning1674 q) (meaning1683 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1674 = false ∨ valuation q 1683 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1680 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1680)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 2 1 (meaning1647 q) (meaning1670 q) (meaning1680 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1670 = false ∨ valuation q 1680 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1681 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1681)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 2 2 (meaning1647 q) (meaning1671 q) (meaning1681 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1671 = false ∨ valuation q 1681 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1682 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1682)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 2 3 (meaning1647 q) (meaning1672 q) (meaning1682 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1672 = false ∨ valuation q 1682 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1683 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1683)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 2 4 (meaning1647 q) (meaning1673 q) (meaning1683 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1673 = false ∨ valuation q 1683 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1684 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1674)) (literal (valuationOf q) (1684)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 2 5 (meaning1647 q) (meaning1674 q) (meaning1684 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1674 = false ∨ valuation q 1684 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1680 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_left (literal (valuationOf q) (1648)) (literal (valuationOf q) (1680)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 3 (meaning1648 q) (meaning1680 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1680 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1681 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1681)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 3 1 (meaning1648 q) (meaning1670 q) (meaning1681 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1670 = false ∨ valuation q 1681 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1682 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1682)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 3 2 (meaning1648 q) (meaning1671 q) (meaning1682 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1671 = false ∨ valuation q 1682 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1683 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1683)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 3 3 (meaning1648 q) (meaning1672 q) (meaning1683 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1672 = false ∨ valuation q 1683 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1684 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1684)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 3 4 (meaning1648 q) (meaning1673 q) (meaning1684 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1673 = false ∨ valuation q 1684 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1681 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_left (literal (valuationOf q) (1649)) (literal (valuationOf q) (1681)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 4 (meaning1649 q) (meaning1681 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1681 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1682 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1682)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 4 1 (meaning1649 q) (meaning1670 q) (meaning1682 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1670 = false ∨ valuation q 1682 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1683 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1683)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 4 2 (meaning1649 q) (meaning1671 q) (meaning1683 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1671 = false ∨ valuation q 1683 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1684 = true := by
  have hs : count1678 q = (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) + (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41, -44]) (l₂ := [-45, -49, -52, -53, -55, -57, -58, -62])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1684)) (countLit q [-31, -32, -34, -37, -38, -40, -41, -44]) (countLit q [-45, -49, -52, -53, -55, -57, -58, -62]) (count1678 q) 4 3 (meaning1649 q) (meaning1672 q) (meaning1684 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1672 = false ∨ valuation q 1684 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E055.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112055
