import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1662 = true := by
  have hs : count1661 q = (countLit q [-71, -72]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-71, -72]) (l₂ := [-74, -76])
  have hm := merge_left (literal (valuationOf q) (1658)) (literal (valuationOf q) (1662)) (countLit q [-71, -72]) (countLit q [-74, -76]) (count1661 q) 2 (meaning1658 q) (meaning1662 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1662 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1663 = true := by
  have hs : count1661 q = (countLit q [-71, -72]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-71, -72]) (l₂ := [-74, -76])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1663)) (countLit q [-71, -72]) (countLit q [-74, -76]) (count1661 q) 2 1 (meaning1658 q) (meaning1659 q) (meaning1663 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1659 = false ∨ valuation q 1663 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1664 = true := by
  have hs : count1661 q = (countLit q [-71, -72]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-71, -72]) (l₂ := [-74, -76])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1664)) (countLit q [-71, -72]) (countLit q [-74, -76]) (count1661 q) 2 2 (meaning1658 q) (meaning1660 q) (meaning1664 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1660 = false ∨ valuation q 1664 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1665 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_right (literal (valuationOf q) (1661)) (literal (valuationOf q) (1665)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 1 (meaning1661 q) (meaning1665 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1665 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1666 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_right (literal (valuationOf q) (1662)) (literal (valuationOf q) (1666)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 2 (meaning1662 q) (meaning1666 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1666 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1667 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_right (literal (valuationOf q) (1663)) (literal (valuationOf q) (1667)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 3 (meaning1663 q) (meaning1667 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1667 = true := counterClause1542 (baseVal q)

theorem counterClause1543 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1668 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_right (literal (valuationOf q) (1664)) (literal (valuationOf q) (1668)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 4 (meaning1664 q) (meaning1668 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1668 = true := counterClause1543 (baseVal q)

theorem counterClause1544 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1665 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_left (literal (valuationOf q) (1654)) (literal (valuationOf q) (1665)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 1 (meaning1654 q) (meaning1665 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1665 = true := counterClause1544 (baseVal q)

theorem counterClause1545 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1666 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1666)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 1 1 (meaning1654 q) (meaning1661 q) (meaning1666 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1661 = false ∨ valuation q 1666 = true := counterClause1545 (baseVal q)

theorem counterClause1546 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1667 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1667)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 1 2 (meaning1654 q) (meaning1662 q) (meaning1667 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1662 = false ∨ valuation q 1667 = true := counterClause1546 (baseVal q)

theorem counterClause1547 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1668 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1668)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 1 3 (meaning1654 q) (meaning1663 q) (meaning1668 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1663 = false ∨ valuation q 1668 = true := counterClause1547 (baseVal q)

theorem counterClause1548 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1666 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_left (literal (valuationOf q) (1655)) (literal (valuationOf q) (1666)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 2 (meaning1655 q) (meaning1666 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1666 = true := counterClause1548 (baseVal q)

theorem counterClause1549 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1667 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1667)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 2 1 (meaning1655 q) (meaning1661 q) (meaning1667 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1661 = false ∨ valuation q 1667 = true := counterClause1549 (baseVal q)

theorem counterClause1550 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1668 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1668)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 2 2 (meaning1655 q) (meaning1662 q) (meaning1668 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1662 = false ∨ valuation q 1668 = true := counterClause1550 (baseVal q)

theorem counterClause1551 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1669 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1669)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 2 3 (meaning1655 q) (meaning1663 q) (meaning1669 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1663 = false ∨ valuation q 1669 = true := counterClause1551 (baseVal q)

theorem counterClause1552 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1667 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_left (literal (valuationOf q) (1656)) (literal (valuationOf q) (1667)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 3 (meaning1656 q) (meaning1667 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1667 = true := counterClause1552 (baseVal q)

theorem counterClause1553 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1668 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1668)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 3 1 (meaning1656 q) (meaning1661 q) (meaning1668 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1661 = false ∨ valuation q 1668 = true := counterClause1553 (baseVal q)

theorem counterClause1554 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1669 = true := by
  have hs : count1665 q = (countLit q [-64, -66, -68]) + (countLit q [-71, -72, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68]) (l₂ := [-71, -72, -74, -76])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1669)) (countLit q [-64, -66, -68]) (countLit q [-71, -72, -74, -76]) (count1665 q) 3 2 (meaning1656 q) (meaning1662 q) (meaning1669 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1662 = false ∨ valuation q 1669 = true := counterClause1554 (baseVal q)

theorem counterClause1555 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1672 = true := by
  have hs : count1672 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1672)) (countLit q [-78]) (countLit q [-81]) (count1672 q) 1 (meaningNeg81 q) (meaning1672 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1672 = true := counterClause1555 (baseVal q)

theorem counterClause1556 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1672 = true := by
  have hs : count1672 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1672)) (countLit q [-78]) (countLit q [-81]) (count1672 q) 1 (meaningNeg78 q) (meaning1672 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1672 = true := counterClause1556 (baseVal q)

theorem counterClause1557 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1673 = true := by
  have hs : count1672 q = (countLit q [-78]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1673)) (countLit q [-78]) (countLit q [-81]) (count1672 q) 1 1 (meaningNeg78 q) (meaningNeg81 q) (meaning1673 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 81 = true ∨ valuation q 1673 = true := counterClause1557 (baseVal q)

theorem counterClause1558 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1674 = true := by
  have hs : count1674 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1674)) (countLit q [-83]) (countLit q [-85]) (count1674 q) 1 (meaningNeg85 q) (meaning1674 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1674 = true := counterClause1558 (baseVal q)

theorem counterClause1559 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1674 = true := by
  have hs : count1674 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1674)) (countLit q [-83]) (countLit q [-85]) (count1674 q) 1 (meaningNeg83 q) (meaning1674 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1674 = true := counterClause1559 (baseVal q)

theorem counterClause1560 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 85 = true ∨ valuationOf q 1675 = true := by
  have hs : count1674 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (1675)) (countLit q [-83]) (countLit q [-85]) (count1674 q) 1 1 (meaningNeg83 q) (meaningNeg85 q) (meaning1675 q) hs
  change (! (valuationOf q 83)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 85 = true ∨ valuation q 1675 = true := counterClause1560 (baseVal q)

theorem counterClause1561 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1676 = true := by
  have hs : count1676 q = (countLit q [-78, -81]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-83, -85])
  have hm := merge_right (literal (valuationOf q) (1674)) (literal (valuationOf q) (1676)) (countLit q [-78, -81]) (countLit q [-83, -85]) (count1676 q) 1 (meaning1674 q) (meaning1676 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1676 = true := counterClause1561 (baseVal q)

theorem counterClause1562 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1677 = true := by
  have hs : count1676 q = (countLit q [-78, -81]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-83, -85])
  have hm := merge_right (literal (valuationOf q) (1675)) (literal (valuationOf q) (1677)) (countLit q [-78, -81]) (countLit q [-83, -85]) (count1676 q) 2 (meaning1675 q) (meaning1677 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1677 = true := counterClause1562 (baseVal q)

theorem counterClause1563 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1676 = true := by
  have hs : count1676 q = (countLit q [-78, -81]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-83, -85])
  have hm := merge_left (literal (valuationOf q) (1672)) (literal (valuationOf q) (1676)) (countLit q [-78, -81]) (countLit q [-83, -85]) (count1676 q) 1 (meaning1672 q) (meaning1676 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1676 = true := counterClause1563 (baseVal q)

theorem counterClause1564 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1677 = true := by
  have hs : count1676 q = (countLit q [-78, -81]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-83, -85])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1674)) (literal (valuationOf q) (1677)) (countLit q [-78, -81]) (countLit q [-83, -85]) (count1676 q) 1 1 (meaning1672 q) (meaning1674 q) (meaning1677 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1674 = false ∨ valuation q 1677 = true := counterClause1564 (baseVal q)

theorem counterClause1565 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1678 = true := by
  have hs : count1676 q = (countLit q [-78, -81]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-83, -85])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1675)) (literal (valuationOf q) (1678)) (countLit q [-78, -81]) (countLit q [-83, -85]) (count1676 q) 1 2 (meaning1672 q) (meaning1675 q) (meaning1678 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1675 = false ∨ valuation q 1678 = true := counterClause1565 (baseVal q)

theorem counterClause1566 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1677 = true := by
  have hs : count1676 q = (countLit q [-78, -81]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-83, -85])
  have hm := merge_left (literal (valuationOf q) (1673)) (literal (valuationOf q) (1677)) (countLit q [-78, -81]) (countLit q [-83, -85]) (count1676 q) 2 (meaning1673 q) (meaning1677 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1677 = true := counterClause1566 (baseVal q)

theorem counterClause1567 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1678 = true := by
  have hs : count1676 q = (countLit q [-78, -81]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-83, -85])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1674)) (literal (valuationOf q) (1678)) (countLit q [-78, -81]) (countLit q [-83, -85]) (count1676 q) 2 1 (meaning1673 q) (meaning1674 q) (meaning1678 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1674 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1674 = false ∨ valuation q 1678 = true := counterClause1567 (baseVal q)

theorem counterClause1568 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1679 = true := by
  have hs : count1676 q = (countLit q [-78, -81]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -81]) (l₂ := [-83, -85])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1675)) (literal (valuationOf q) (1679)) (countLit q [-78, -81]) (countLit q [-83, -85]) (count1676 q) 2 2 (meaning1673 q) (meaning1675 q) (meaning1679 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1675 = false ∨ valuation q 1679 = true := counterClause1568 (baseVal q)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E105.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112105
