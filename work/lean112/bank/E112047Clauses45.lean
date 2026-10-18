import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1671 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1671)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 6 3 (meaning1641 q) (meaning1658 q) (meaning1671 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1658 = false ∨ valuation q 1671 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1682 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1682)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 1 5 (meaning1609 q) (meaning1667 q) (meaning1682 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1667 = false ∨ valuation q 1682 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1683 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1683)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 1 6 (meaning1609 q) (meaning1668 q) (meaning1683 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1668 = false ∨ valuation q 1683 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1684 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1684)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 1 7 (meaning1609 q) (meaning1669 q) (meaning1684 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1669 = false ∨ valuation q 1684 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1681 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1681)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 2 3 (meaning1610 q) (meaning1665 q) (meaning1681 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1665 = false ∨ valuation q 1681 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1682 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1682)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 2 4 (meaning1610 q) (meaning1666 q) (meaning1682 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1666 = false ∨ valuation q 1682 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1683 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1683)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 2 5 (meaning1610 q) (meaning1667 q) (meaning1683 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1667 = false ∨ valuation q 1683 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1684 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1684)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 2 6 (meaning1610 q) (meaning1668 q) (meaning1684 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1668 = false ∨ valuation q 1684 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1685 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1685)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 2 7 (meaning1610 q) (meaning1669 q) (meaning1685 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1669 = false ∨ valuation q 1685 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1686 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1686)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 2 8 (meaning1610 q) (meaning1670 q) (meaning1686 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1670 = false ∨ valuation q 1686 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1687 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1671)) (literal (valuationOf q) (1687)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 2 9 (meaning1610 q) (meaning1671 q) (meaning1687 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1671 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1671 = false ∨ valuation q 1687 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1680 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1680)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 3 1 (meaning1611 q) (meaning1663 q) (meaning1680 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1663 = false ∨ valuation q 1680 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1681 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1681)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 3 2 (meaning1611 q) (meaning1664 q) (meaning1681 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1664 = false ∨ valuation q 1681 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1682 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1682)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 3 3 (meaning1611 q) (meaning1665 q) (meaning1682 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1665 = false ∨ valuation q 1682 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1683 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1683)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 3 4 (meaning1611 q) (meaning1666 q) (meaning1683 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1666 = false ∨ valuation q 1683 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1684 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1684)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 3 5 (meaning1611 q) (meaning1667 q) (meaning1684 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1667 = false ∨ valuation q 1684 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1685 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1685)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 3 6 (meaning1611 q) (meaning1668 q) (meaning1685 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1668 = false ∨ valuation q 1685 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1686 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1686)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 3 7 (meaning1611 q) (meaning1669 q) (meaning1686 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1669 = false ∨ valuation q 1686 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1681 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1681)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 4 1 (meaning1612 q) (meaning1663 q) (meaning1681 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1663 = false ∨ valuation q 1681 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1682 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1682)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 4 2 (meaning1612 q) (meaning1664 q) (meaning1682 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1664 = false ∨ valuation q 1682 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1683 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1683)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 4 3 (meaning1612 q) (meaning1665 q) (meaning1683 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1665 = false ∨ valuation q 1683 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1684 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1684)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 4 4 (meaning1612 q) (meaning1666 q) (meaning1684 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1666 = false ∨ valuation q 1684 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1685 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1685)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 4 5 (meaning1612 q) (meaning1667 q) (meaning1685 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1667 = false ∨ valuation q 1685 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1686 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1686)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 4 6 (meaning1612 q) (meaning1668 q) (meaning1686 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1668 = false ∨ valuation q 1686 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1687 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1687)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 4 7 (meaning1612 q) (meaning1669 q) (meaning1687 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1669 = false ∨ valuation q 1687 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1682 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1682)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 5 1 (meaning1613 q) (meaning1663 q) (meaning1682 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1663 = false ∨ valuation q 1682 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1683 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1683)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 5 2 (meaning1613 q) (meaning1664 q) (meaning1683 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1664 = false ∨ valuation q 1683 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1684 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1684)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 5 3 (meaning1613 q) (meaning1665 q) (meaning1684 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1665 = false ∨ valuation q 1684 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1685 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1685)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 5 4 (meaning1613 q) (meaning1666 q) (meaning1685 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1666 = false ∨ valuation q 1685 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1686 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1686)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 5 5 (meaning1613 q) (meaning1667 q) (meaning1686 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1667 = false ∨ valuation q 1686 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1687 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1687)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 5 6 (meaning1613 q) (meaning1668 q) (meaning1687 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1668 = false ∨ valuation q 1687 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1688 = true := by
  have hs : count1677 q = (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) + (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (l₂ := [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1688)) (countLit q [-63, -64, -66, -67, -71, -73, -75, -76, -80, -82, -84, -85, -89, -91]) (countLit q [-92, -93, -96, -97, -101, -103, -104, -105, -108, -110, -111, -113, -115, -117]) (count1677 q) 5 7 (meaning1613 q) (meaning1669 q) (meaning1688 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1669 = false ∨ valuation q 1688 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E047.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112047
