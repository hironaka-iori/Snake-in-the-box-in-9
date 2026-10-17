import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec51 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1633 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1664 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1664)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 1 1 (meaning1652 q) (meaning1659 q) (meaning1664 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1633 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1659 = false ∨ valuation q 1664 = true := counterClause1633 (baseVal q)

theorem counterClause1634 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1665 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1665)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 1 2 (meaning1652 q) (meaning1660 q) (meaning1665 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1634 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1660 = false ∨ valuation q 1665 = true := counterClause1634 (baseVal q)

theorem counterClause1635 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1666 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1666)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 1 3 (meaning1652 q) (meaning1661 q) (meaning1666 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1635 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1661 = false ∨ valuation q 1666 = true := counterClause1635 (baseVal q)

theorem counterClause1636 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1667 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1667)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 1 4 (meaning1652 q) (meaning1662 q) (meaning1667 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1636 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1662 = false ∨ valuation q 1667 = true := counterClause1636 (baseVal q)

theorem counterClause1637 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1664 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_left (literal (valuationOf q) (1653)) (literal (valuationOf q) (1664)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 2 (meaning1653 q) (meaning1664 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1637 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1664 = true := counterClause1637 (baseVal q)

theorem counterClause1638 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1665 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1665)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 2 1 (meaning1653 q) (meaning1659 q) (meaning1665 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1638 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1659 = false ∨ valuation q 1665 = true := counterClause1638 (baseVal q)

theorem counterClause1639 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1666 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1666)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 2 2 (meaning1653 q) (meaning1660 q) (meaning1666 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1639 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1660 = false ∨ valuation q 1666 = true := counterClause1639 (baseVal q)

theorem counterClause1640 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1667 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1667)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 2 3 (meaning1653 q) (meaning1661 q) (meaning1667 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1640 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1661 = false ∨ valuation q 1667 = true := counterClause1640 (baseVal q)

theorem counterClause1641 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1668 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1668)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 2 4 (meaning1653 q) (meaning1662 q) (meaning1668 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1641 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1662 = false ∨ valuation q 1668 = true := counterClause1641 (baseVal q)

theorem counterClause1642 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1665 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_left (literal (valuationOf q) (1654)) (literal (valuationOf q) (1665)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 3 (meaning1654 q) (meaning1665 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1642 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1665 = true := counterClause1642 (baseVal q)

theorem counterClause1643 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1666 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1666)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 3 1 (meaning1654 q) (meaning1659 q) (meaning1666 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1643 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1659 = false ∨ valuation q 1666 = true := counterClause1643 (baseVal q)

theorem counterClause1644 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1667 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1667)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 3 2 (meaning1654 q) (meaning1660 q) (meaning1667 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1644 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1660 = false ∨ valuation q 1667 = true := counterClause1644 (baseVal q)

theorem counterClause1645 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1668 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1668)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 3 3 (meaning1654 q) (meaning1661 q) (meaning1668 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1645 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1661 = false ∨ valuation q 1668 = true := counterClause1645 (baseVal q)

theorem counterClause1646 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1669 = true := by
  have hs : count1663 q = (countLit q [-62, -64, -66]) + (countLit q [-67, -69, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66]) (l₂ := [-67, -69, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1669)) (countLit q [-62, -64, -66]) (countLit q [-67, -69, -72, -73]) (count1663 q) 3 4 (meaning1654 q) (meaning1662 q) (meaning1669 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1646 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1662 = false ∨ valuation q 1669 = true := counterClause1646 (baseVal q)

theorem counterClause1647 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1670 = true := by
  have hs : count1670 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1670)) (countLit q [-75]) (countLit q [-76]) (count1670 q) 1 (meaningNeg76 q) (meaning1670 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1647 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1670 = true := counterClause1647 (baseVal q)

theorem counterClause1648 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1670 = true := by
  have hs : count1670 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1670)) (countLit q [-75]) (countLit q [-76]) (count1670 q) 1 (meaningNeg75 q) (meaning1670 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1648 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1670 = true := counterClause1648 (baseVal q)

theorem counterClause1649 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1671 = true := by
  have hs : count1670 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1671)) (countLit q [-75]) (countLit q [-76]) (count1670 q) 1 1 (meaningNeg75 q) (meaningNeg76 q) (meaning1671 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1649 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 76 = true ∨ valuation q 1671 = true := counterClause1649 (baseVal q)

theorem counterClause1650 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1672 = true := by
  have hs : count1672 q = (countLit q [-79]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1672)) (countLit q [-79]) (countLit q [-81]) (count1672 q) 1 (meaningNeg81 q) (meaning1672 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1650 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1672 = true := counterClause1650 (baseVal q)

theorem counterClause1651 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1672 = true := by
  have hs : count1672 q = (countLit q [-79]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1672)) (countLit q [-79]) (countLit q [-81]) (count1672 q) 1 (meaningNeg79 q) (meaning1672 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1651 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1672 = true := counterClause1651 (baseVal q)

theorem counterClause1652 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1673 = true := by
  have hs : count1672 q = (countLit q [-79]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1673)) (countLit q [-79]) (countLit q [-81]) (count1672 q) 1 1 (meaningNeg79 q) (meaningNeg81 q) (meaning1673 q) hs
  change (! (valuationOf q 79)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1652 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 81 = true ∨ valuation q 1673 = true := counterClause1652 (baseVal q)

theorem counterClause1653 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1674 = true := by
  have hs : count1674 q = (countLit q [-75, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -81])
  have hm := merge_right (literal (valuationOf q) (1672)) (literal (valuationOf q) (1674)) (countLit q [-75, -76]) (countLit q [-79, -81]) (count1674 q) 1 (meaning1672 q) (meaning1674 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1653 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1674 = true := counterClause1653 (baseVal q)

theorem counterClause1654 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1675 = true := by
  have hs : count1674 q = (countLit q [-75, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -81])
  have hm := merge_right (literal (valuationOf q) (1673)) (literal (valuationOf q) (1675)) (countLit q [-75, -76]) (countLit q [-79, -81]) (count1674 q) 2 (meaning1673 q) (meaning1675 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1654 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1675 = true := counterClause1654 (baseVal q)

theorem counterClause1655 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1674 = true := by
  have hs : count1674 q = (countLit q [-75, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -81])
  have hm := merge_left (literal (valuationOf q) (1670)) (literal (valuationOf q) (1674)) (countLit q [-75, -76]) (countLit q [-79, -81]) (count1674 q) 1 (meaning1670 q) (meaning1674 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1655 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1674 = true := counterClause1655 (baseVal q)

theorem counterClause1656 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1675 = true := by
  have hs : count1674 q = (countLit q [-75, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -81])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1675)) (countLit q [-75, -76]) (countLit q [-79, -81]) (count1674 q) 1 1 (meaning1670 q) (meaning1672 q) (meaning1675 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1656 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1672 = false ∨ valuation q 1675 = true := counterClause1656 (baseVal q)

theorem counterClause1657 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1676 = true := by
  have hs : count1674 q = (countLit q [-75, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -81])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1676)) (countLit q [-75, -76]) (countLit q [-79, -81]) (count1674 q) 1 2 (meaning1670 q) (meaning1673 q) (meaning1676 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1657 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1673 = false ∨ valuation q 1676 = true := counterClause1657 (baseVal q)

theorem counterClause1658 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1675 = true := by
  have hs : count1674 q = (countLit q [-75, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -81])
  have hm := merge_left (literal (valuationOf q) (1671)) (literal (valuationOf q) (1675)) (countLit q [-75, -76]) (countLit q [-79, -81]) (count1674 q) 2 (meaning1671 q) (meaning1675 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1658 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1675 = true := counterClause1658 (baseVal q)

theorem counterClause1659 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1676 = true := by
  have hs : count1674 q = (countLit q [-75, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -81])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1676)) (countLit q [-75, -76]) (countLit q [-79, -81]) (count1674 q) 2 1 (meaning1671 q) (meaning1672 q) (meaning1676 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1659 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1672 = false ∨ valuation q 1676 = true := counterClause1659 (baseVal q)

theorem counterClause1660 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1677 = true := by
  have hs : count1674 q = (countLit q [-75, -76]) + (countLit q [-79, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -81])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1673)) (literal (valuationOf q) (1677)) (countLit q [-75, -76]) (countLit q [-79, -81]) (count1674 q) 2 2 (meaning1671 q) (meaning1673 q) (meaning1677 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1673 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1660 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1673 = false ∨ valuation q 1677 = true := counterClause1660 (baseVal q)

theorem counterClause1661 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1678 = true := by
  have hs : count1678 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (1678)) (countLit q [-85]) (countLit q [-87]) (count1678 q) 1 (meaningNeg87 q) (meaning1678 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1661 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1678 = true := counterClause1661 (baseVal q)

theorem counterClause1662 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1678 = true := by
  have hs : count1678 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1678)) (countLit q [-85]) (countLit q [-87]) (count1678 q) 1 (meaningNeg85 q) (meaning1678 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1662 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1678 = true := counterClause1662 (baseVal q)

theorem counterClause1663 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 87 = true ∨ valuationOf q 1679 = true := by
  have hs : count1678 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-87)) (literal (valuationOf q) (1679)) (countLit q [-85]) (countLit q [-87]) (count1678 q) 1 1 (meaningNeg85 q) (meaningNeg87 q) (meaning1679 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 87)) = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1663 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 87 = true ∨ valuation q 1679 = true := counterClause1663 (baseVal q)

theorem counterClause1664 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1680 = true := by
  have hs : count1680 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (1680)) (countLit q [-89]) (countLit q [-91]) (count1680 q) 1 (meaningNeg91 q) (meaning1680 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1664 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1680 = true := counterClause1664 (baseVal q)

theorem block51 (q : Snake 81) (h : Conditions q) : B112E089.Block51 (valuation q) :=
  ⟨clause1633 q h, clause1634 q h, clause1635 q h, clause1636 q h, clause1637 q h, clause1638 q h, clause1639 q h, clause1640 q h, clause1641 q h, clause1642 q h, clause1643 q h, clause1644 q h, clause1645 q h, clause1646 q h, clause1647 q h, clause1648 q h, clause1649 q h, clause1650 q h, clause1651 q h, clause1652 q h, clause1653 q h, clause1654 q h, clause1655 q h, clause1656 q h, clause1657 q h, clause1658 q h, clause1659 q h, clause1660 q h, clause1661 q h, clause1662 q h, clause1663 q h, clause1664 q h⟩

end
end Snake9.Regrowth.E112089
