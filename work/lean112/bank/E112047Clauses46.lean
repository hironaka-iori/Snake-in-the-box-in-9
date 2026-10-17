import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1683 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1683)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 6 1 (meaning1614 q) (meaning1663 q) (meaning1683 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1663 = false ∨ valuation q 1683 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1684 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1684)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 6 2 (meaning1614 q) (meaning1664 q) (meaning1684 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1664 = false ∨ valuation q 1684 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1685 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1685)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 6 3 (meaning1614 q) (meaning1665 q) (meaning1685 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1665 = false ∨ valuation q 1685 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1686 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1686)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 6 4 (meaning1614 q) (meaning1666 q) (meaning1686 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1666 = false ∨ valuation q 1686 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1687 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1687)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 6 5 (meaning1614 q) (meaning1667 q) (meaning1687 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1667 = false ∨ valuation q 1687 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1688 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1688)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 6 6 (meaning1614 q) (meaning1668 q) (meaning1688 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1668 = false ∨ valuation q 1688 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1689 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1689)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 6 7 (meaning1614 q) (meaning1669 q) (meaning1689 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1669 = false ∨ valuation q 1689 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1684 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1684)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 7 1 (meaning1615 q) (meaning1663 q) (meaning1684 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1663 = false ∨ valuation q 1684 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1685 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1685)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 7 2 (meaning1615 q) (meaning1664 q) (meaning1685 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1664 = false ∨ valuation q 1685 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1686 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1686)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 7 3 (meaning1615 q) (meaning1665 q) (meaning1686 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1665 = false ∨ valuation q 1686 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1687 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1687)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 7 4 (meaning1615 q) (meaning1666 q) (meaning1687 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1666 = false ∨ valuation q 1687 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1688 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1688)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 7 5 (meaning1615 q) (meaning1667 q) (meaning1688 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1667 = false ∨ valuation q 1688 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1685 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1685)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 8 1 (meaning1616 q) (meaning1663 q) (meaning1685 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1663 = false ∨ valuation q 1685 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1686 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1686)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 8 2 (meaning1616 q) (meaning1664 q) (meaning1686 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1664 = false ∨ valuation q 1686 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1687 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1687)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 8 3 (meaning1616 q) (meaning1665 q) (meaning1687 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1665 = false ∨ valuation q 1687 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1688 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1688)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 8 4 (meaning1616 q) (meaning1666 q) (meaning1688 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1666 = false ∨ valuation q 1688 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1689 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1689)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 8 5 (meaning1616 q) (meaning1667 q) (meaning1689 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1667 = false ∨ valuation q 1689 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1686 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1686)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 9 1 (meaning1617 q) (meaning1663 q) (meaning1686 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1663 = false ∨ valuation q 1686 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1687 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1687)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 9 2 (meaning1617 q) (meaning1664 q) (meaning1687 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1664 = false ∨ valuation q 1687 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) + (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (l₂ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1693 q) 3 13 (meaning1555 q) (meaning1689 q) (meaning1708 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1689 = false ∨ valuation q 1708 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) + (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (l₂ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1693 q) 4 12 (meaning1556 q) (meaning1688 q) (meaning1708 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1688 = false ∨ valuation q 1708 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) + (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (l₂ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1693 q) 5 11 (meaning1557 q) (meaning1687 q) (meaning1708 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1687 = false ∨ valuation q 1708 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) + (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (l₂ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1693 q) 6 10 (meaning1558 q) (meaning1686 q) (meaning1708 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1686 = false ∨ valuation q 1708 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) + (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (l₂ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1693 q) 7 9 (meaning1559 q) (meaning1685 q) (meaning1708 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1685 = false ∨ valuation q 1708 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) + (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (l₂ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1693 q) 8 8 (meaning1560 q) (meaning1684 q) (meaning1708 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1684 = false ∨ valuation q 1708 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) + (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (l₂ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1693 q) 9 7 (meaning1561 q) (meaning1683 q) (meaning1708 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1683 = false ∨ valuation q 1708 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) + (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (l₂ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1693 q) 10 6 (meaning1562 q) (meaning1682 q) (meaning1708 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1682 = false ∨ valuation q 1708 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) + (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (l₂ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1693 q) 11 5 (meaning1563 q) (meaning1681 q) (meaning1708 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1681 = false ∨ valuation q 1708 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) + (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (l₂ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91, -92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1693 q) 12 4 (meaning1564 q) (meaning1680 q) (meaning1708 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1680 = false ∨ valuation q 1708 = true := counterClause1501 (baseVal q)

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false := by
  rw [value1708]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1693 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 41 = false ∨ valuation q 72 = false ∨ valuation q 111 = false := by
  rw [value12, value41, value72, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (82 : Vertex) (210 : Vertex) (338 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value14, value15, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (128 : Vertex) (129 : Vertex) (130 : Vertex) (131 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E047.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112047
