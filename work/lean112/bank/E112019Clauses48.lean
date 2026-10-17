import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1658 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1658)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 3 5 (meaning1622 q) (meaning1647 q) (meaning1658 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1647 = false ∨ valuation q 1658 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1659 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1659)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 3 6 (meaning1622 q) (meaning1648 q) (meaning1659 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1648 = false ∨ valuation q 1659 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1660 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1660)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 3 7 (meaning1622 q) (meaning1649 q) (meaning1660 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1649 = false ∨ valuation q 1660 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1654 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_left (literal (valuationOf q) (1623)) (literal (valuationOf q) (1654)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 4 (meaning1623 q) (meaning1654 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1654 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1655 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1655)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 4 1 (meaning1623 q) (meaning1643 q) (meaning1655 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1643 = false ∨ valuation q 1655 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1656 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1656)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 4 2 (meaning1623 q) (meaning1644 q) (meaning1656 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1644 = false ∨ valuation q 1656 = true := counterClause1542 (baseVal q)

theorem counterClause1543 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1657 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1657)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 4 3 (meaning1623 q) (meaning1645 q) (meaning1657 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1645 = false ∨ valuation q 1657 = true := counterClause1543 (baseVal q)

theorem counterClause1544 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1658 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1658)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 4 4 (meaning1623 q) (meaning1646 q) (meaning1658 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1646 = false ∨ valuation q 1658 = true := counterClause1544 (baseVal q)

theorem counterClause1545 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1659 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1659)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 4 5 (meaning1623 q) (meaning1647 q) (meaning1659 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1647 = false ∨ valuation q 1659 = true := counterClause1545 (baseVal q)

theorem counterClause1546 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1655 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_left (literal (valuationOf q) (1624)) (literal (valuationOf q) (1655)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 5 (meaning1624 q) (meaning1655 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1655 = true := counterClause1546 (baseVal q)

theorem counterClause1547 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1656 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1656)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 5 1 (meaning1624 q) (meaning1643 q) (meaning1656 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1643 = false ∨ valuation q 1656 = true := counterClause1547 (baseVal q)

theorem counterClause1548 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1657 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1657)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 5 2 (meaning1624 q) (meaning1644 q) (meaning1657 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1644 = false ∨ valuation q 1657 = true := counterClause1548 (baseVal q)

theorem counterClause1549 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1658 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1658)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 5 3 (meaning1624 q) (meaning1645 q) (meaning1658 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1645 = false ∨ valuation q 1658 = true := counterClause1549 (baseVal q)

theorem counterClause1550 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1659 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1659)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 5 4 (meaning1624 q) (meaning1646 q) (meaning1659 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1646 = false ∨ valuation q 1659 = true := counterClause1550 (baseVal q)

theorem counterClause1551 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1657 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1657)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 6 1 (meaning1625 q) (meaning1643 q) (meaning1657 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1643 = false ∨ valuation q 1657 = true := counterClause1551 (baseVal q)

theorem counterClause1552 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1658 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1658)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 6 2 (meaning1625 q) (meaning1644 q) (meaning1658 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1644 = false ∨ valuation q 1658 = true := counterClause1552 (baseVal q)

theorem counterClause1553 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1659 = true := by
  have hs : count1651 q = (countLit q [-63, -64, -66, -67, -69, -71, -72]) + (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72]) (l₂ := [-75, -76, -80, -81, -82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1659)) (countLit q [-63, -64, -66, -67, -69, -71, -72]) (countLit q [-75, -76, -80, -81, -82, -85, -87, -89]) (count1651 q) 6 3 (meaning1625 q) (meaning1645 q) (meaning1659 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1645 = false ∨ valuation q 1659 = true := counterClause1553 (baseVal q)

theorem counterClause1554 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1666 = true := by
  have hs : count1666 q = (countLit q [-92]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-95])
  have hm := merge_right (literal (valuationOf q) (-95)) (literal (valuationOf q) (1666)) (countLit q [-92]) (countLit q [-95]) (count1666 q) 1 (meaningNeg95 q) (meaning1666 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1666 = true := counterClause1554 (baseVal q)

theorem counterClause1555 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1666 = true := by
  have hs : count1666 q = (countLit q [-92]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1666)) (countLit q [-92]) (countLit q [-95]) (count1666 q) 1 (meaningNeg92 q) (meaning1666 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1666 = true := counterClause1555 (baseVal q)

theorem counterClause1556 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 95 = true ∨ valuationOf q 1667 = true := by
  have hs : count1666 q = (countLit q [-92]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-95])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-95)) (literal (valuationOf q) (1667)) (countLit q [-92]) (countLit q [-95]) (count1666 q) 1 1 (meaningNeg92 q) (meaningNeg95 q) (meaning1667 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 95)) = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 95 = true ∨ valuation q 1667 = true := counterClause1556 (baseVal q)

theorem counterClause1557 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1668 = true := by
  have hs : count1668 q = (countLit q [-91]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -95])
  have hm := merge_right (literal (valuationOf q) (1666)) (literal (valuationOf q) (1668)) (countLit q [-91]) (countLit q [-92, -95]) (count1668 q) 1 (meaning1666 q) (meaning1668 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1668 = true := counterClause1557 (baseVal q)

theorem counterClause1558 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1669 = true := by
  have hs : count1668 q = (countLit q [-91]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -95])
  have hm := merge_right (literal (valuationOf q) (1667)) (literal (valuationOf q) (1669)) (countLit q [-91]) (countLit q [-92, -95]) (count1668 q) 2 (meaning1667 q) (meaning1669 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1669 = true := counterClause1558 (baseVal q)

theorem counterClause1559 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1668 = true := by
  have hs : count1668 q = (countLit q [-91]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -95])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1668)) (countLit q [-91]) (countLit q [-92, -95]) (count1668 q) 1 (meaningNeg91 q) (meaning1668 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1668 = true := counterClause1559 (baseVal q)

theorem counterClause1560 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1666 = false ∨ valuationOf q 1669 = true := by
  have hs : count1668 q = (countLit q [-91]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -95])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1669)) (countLit q [-91]) (countLit q [-92, -95]) (count1668 q) 1 1 (meaningNeg91 q) (meaning1666 q) (meaning1669 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1666 = false ∨ valuation q 1669 = true := counterClause1560 (baseVal q)

theorem counterClause1561 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1667 = false ∨ valuationOf q 1670 = true := by
  have hs : count1668 q = (countLit q [-91]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -95])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1670)) (countLit q [-91]) (countLit q [-92, -95]) (count1668 q) 1 2 (meaningNeg91 q) (meaning1667 q) (meaning1670 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1667 = false ∨ valuation q 1670 = true := counterClause1561 (baseVal q)

theorem counterClause1562 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1671 = true := by
  have hs : count1671 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1671)) (countLit q [-98]) (countLit q [-99]) (count1671 q) 1 (meaningNeg99 q) (meaning1671 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1671 = true := counterClause1562 (baseVal q)

theorem counterClause1563 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1671 = true := by
  have hs : count1671 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1671)) (countLit q [-98]) (countLit q [-99]) (count1671 q) 1 (meaningNeg98 q) (meaning1671 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1671 = true := counterClause1563 (baseVal q)

theorem counterClause1564 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 99 = true ∨ valuationOf q 1672 = true := by
  have hs : count1671 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-99)) (literal (valuationOf q) (1672)) (countLit q [-98]) (countLit q [-99]) (count1671 q) 1 1 (meaningNeg98 q) (meaningNeg99 q) (meaning1672 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 99)) = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 99 = true ∨ valuation q 1672 = true := counterClause1564 (baseVal q)

theorem counterClause1565 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1673 = true := by
  have hs : count1673 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_right (literal (valuationOf q) (-103)) (literal (valuationOf q) (1673)) (countLit q [-102]) (countLit q [-103]) (count1673 q) 1 (meaningNeg103 q) (meaning1673 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1673 = true := counterClause1565 (baseVal q)

theorem counterClause1566 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1673 = true := by
  have hs : count1673 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1673)) (countLit q [-102]) (countLit q [-103]) (count1673 q) 1 (meaningNeg102 q) (meaning1673 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1673 = true := counterClause1566 (baseVal q)

theorem counterClause1567 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 103 = true ∨ valuationOf q 1674 = true := by
  have hs : count1673 q = (countLit q [-102]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-103])
  have hm := merge_two (literal (valuationOf q) (-102)) (literal (valuationOf q) (-103)) (literal (valuationOf q) (1674)) (countLit q [-102]) (countLit q [-103]) (count1673 q) 1 1 (meaningNeg102 q) (meaningNeg103 q) (meaning1674 q) hs
  change (! (valuationOf q 102)) = false ∨ (! (valuationOf q 103)) = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 103 = true ∨ valuation q 1674 = true := counterClause1567 (baseVal q)

theorem counterClause1568 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1675 = true := by
  have hs : count1675 q = (countLit q [-98, -99]) + (countLit q [-102, -103]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -103])
  have hm := merge_right (literal (valuationOf q) (1673)) (literal (valuationOf q) (1675)) (countLit q [-98, -99]) (countLit q [-102, -103]) (count1675 q) 1 (meaning1673 q) (meaning1675 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1675 = true := counterClause1568 (baseVal q)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E019.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112019
