import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1659)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 2 3 (meaning1644 q) (meaning1653 q) (meaning1659 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1653 = false ∨ valuation q 1659 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1660)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 2 4 (meaning1644 q) (meaning1654 q) (meaning1660 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1654 = false ∨ valuation q 1660 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1645)) (literal (valuationOf q) (1657)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 3 (meaning1645 q) (meaning1657 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1657 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1658)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 3 1 (meaning1645 q) (meaning1651 q) (meaning1658 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1651 = false ∨ valuation q 1658 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1659)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 3 2 (meaning1645 q) (meaning1652 q) (meaning1659 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1652 = false ∨ valuation q 1659 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1660)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 3 3 (meaning1645 q) (meaning1653 q) (meaning1660 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1653 = false ∨ valuation q 1660 = true := counterClause1542 (baseVal q)

theorem counterClause1543 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1646)) (literal (valuationOf q) (1658)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 4 (meaning1646 q) (meaning1658 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1658 = true := counterClause1543 (baseVal q)

theorem counterClause1544 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1659)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 4 1 (meaning1646 q) (meaning1651 q) (meaning1659 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1651 = false ∨ valuation q 1659 = true := counterClause1544 (baseVal q)

theorem counterClause1545 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-90, -91, -97, -98]) + (countLit q [-101, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -91, -97, -98]) (l₂ := [-101, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1660)) (countLit q [-90, -91, -97, -98]) (countLit q [-101, -102, -103, -105]) (count1655 q) 4 2 (meaning1646 q) (meaning1652 q) (meaning1660 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1652 = false ∨ valuation q 1660 = true := counterClause1545 (baseVal q)

theorem counterClause1546 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1663 = true := by
  have hs : count1663 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1663)) (countLit q [-106]) (countLit q [-108]) (count1663 q) 1 (meaningNeg108 q) (meaning1663 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1663 = true := counterClause1546 (baseVal q)

theorem counterClause1547 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1663 = true := by
  have hs : count1663 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1663)) (countLit q [-106]) (countLit q [-108]) (count1663 q) 1 (meaningNeg106 q) (meaning1663 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1663 = true := counterClause1547 (baseVal q)

theorem counterClause1548 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1664 = true := by
  have hs : count1663 q = (countLit q [-106]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-106)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1664)) (countLit q [-106]) (countLit q [-108]) (count1663 q) 1 1 (meaningNeg106 q) (meaningNeg108 q) (meaning1664 q) hs
  change (! (valuationOf q 106)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 1664 = true := counterClause1548 (baseVal q)

theorem counterClause1549 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1665 = true := by
  have hs : count1665 q = (countLit q [-109]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-111])
  have hm := merge_right (literal (valuationOf q) (-111)) (literal (valuationOf q) (1665)) (countLit q [-109]) (countLit q [-111]) (count1665 q) 1 (meaningNeg111 q) (meaning1665 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1665 = true := counterClause1549 (baseVal q)

theorem counterClause1550 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1665 = true := by
  have hs : count1665 q = (countLit q [-109]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-111])
  have hm := merge_left (literal (valuationOf q) (-109)) (literal (valuationOf q) (1665)) (countLit q [-109]) (countLit q [-111]) (count1665 q) 1 (meaningNeg109 q) (meaning1665 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1665 = true := counterClause1550 (baseVal q)

theorem counterClause1551 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 111 = true ∨ valuationOf q 1666 = true := by
  have hs : count1665 q = (countLit q [-109]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-111])
  have hm := merge_two (literal (valuationOf q) (-109)) (literal (valuationOf q) (-111)) (literal (valuationOf q) (1666)) (countLit q [-109]) (countLit q [-111]) (count1665 q) 1 1 (meaningNeg109 q) (meaningNeg111 q) (meaning1666 q) hs
  change (! (valuationOf q 109)) = false ∨ (! (valuationOf q 111)) = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 1666 = true := counterClause1551 (baseVal q)

theorem counterClause1552 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1667 = true := by
  have hs : count1667 q = (countLit q [-106, -108]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-109, -111])
  have hm := merge_right (literal (valuationOf q) (1665)) (literal (valuationOf q) (1667)) (countLit q [-106, -108]) (countLit q [-109, -111]) (count1667 q) 1 (meaning1665 q) (meaning1667 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1667 = true := counterClause1552 (baseVal q)

theorem counterClause1553 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1668 = true := by
  have hs : count1667 q = (countLit q [-106, -108]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-109, -111])
  have hm := merge_right (literal (valuationOf q) (1666)) (literal (valuationOf q) (1668)) (countLit q [-106, -108]) (countLit q [-109, -111]) (count1667 q) 2 (meaning1666 q) (meaning1668 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1668 = true := counterClause1553 (baseVal q)

theorem counterClause1554 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1667 = true := by
  have hs : count1667 q = (countLit q [-106, -108]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-109, -111])
  have hm := merge_left (literal (valuationOf q) (1663)) (literal (valuationOf q) (1667)) (countLit q [-106, -108]) (countLit q [-109, -111]) (count1667 q) 1 (meaning1663 q) (meaning1667 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1667 = true := counterClause1554 (baseVal q)

theorem counterClause1555 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1668 = true := by
  have hs : count1667 q = (countLit q [-106, -108]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-109, -111])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1668)) (countLit q [-106, -108]) (countLit q [-109, -111]) (count1667 q) 1 1 (meaning1663 q) (meaning1665 q) (meaning1668 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1665 = false ∨ valuation q 1668 = true := counterClause1555 (baseVal q)

theorem counterClause1556 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1669 = true := by
  have hs : count1667 q = (countLit q [-106, -108]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-109, -111])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1669)) (countLit q [-106, -108]) (countLit q [-109, -111]) (count1667 q) 1 2 (meaning1663 q) (meaning1666 q) (meaning1669 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1666 = false ∨ valuation q 1669 = true := counterClause1556 (baseVal q)

theorem counterClause1557 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1668 = true := by
  have hs : count1667 q = (countLit q [-106, -108]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-109, -111])
  have hm := merge_left (literal (valuationOf q) (1664)) (literal (valuationOf q) (1668)) (countLit q [-106, -108]) (countLit q [-109, -111]) (count1667 q) 2 (meaning1664 q) (meaning1668 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1668 = true := counterClause1557 (baseVal q)

theorem counterClause1558 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1669 = true := by
  have hs : count1667 q = (countLit q [-106, -108]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-109, -111])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1669)) (countLit q [-106, -108]) (countLit q [-109, -111]) (count1667 q) 2 1 (meaning1664 q) (meaning1665 q) (meaning1669 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1665 = false ∨ valuation q 1669 = true := counterClause1558 (baseVal q)

theorem counterClause1559 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1670 = true := by
  have hs : count1667 q = (countLit q [-106, -108]) + (countLit q [-109, -111]) := List.countP_append (p := literal q) (l₁ := [-106, -108]) (l₂ := [-109, -111])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1670)) (countLit q [-106, -108]) (countLit q [-109, -111]) (count1667 q) 2 2 (meaning1664 q) (meaning1666 q) (meaning1670 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1666 = false ∨ valuation q 1670 = true := counterClause1559 (baseVal q)

theorem counterClause1560 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1671 = true := by
  have hs : count1671 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_right (literal (valuationOf q) (-116)) (literal (valuationOf q) (1671)) (countLit q [-114]) (countLit q [-116]) (count1671 q) 1 (meaningNeg116 q) (meaning1671 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1671 = true := counterClause1560 (baseVal q)

theorem counterClause1561 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1671 = true := by
  have hs : count1671 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_left (literal (valuationOf q) (-114)) (literal (valuationOf q) (1671)) (countLit q [-114]) (countLit q [-116]) (count1671 q) 1 (meaningNeg114 q) (meaning1671 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1671 = true := counterClause1561 (baseVal q)

theorem counterClause1562 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 116 = true ∨ valuationOf q 1672 = true := by
  have hs : count1671 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_two (literal (valuationOf q) (-114)) (literal (valuationOf q) (-116)) (literal (valuationOf q) (1672)) (countLit q [-114]) (countLit q [-116]) (count1671 q) 1 1 (meaningNeg114 q) (meaningNeg116 q) (meaning1672 q) hs
  change (! (valuationOf q 114)) = false ∨ (! (valuationOf q 116)) = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 116 = true ∨ valuation q 1672 = true := counterClause1562 (baseVal q)

theorem counterClause1563 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 1673 = true := by
  have hs : count1673 q = (countLit q [-117]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-119])
  have hm := merge_right (literal (valuationOf q) (-119)) (literal (valuationOf q) (1673)) (countLit q [-117]) (countLit q [-119]) (count1673 q) 1 (meaningNeg119 q) (meaning1673 q) hs
  change (! (valuationOf q 119)) = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 1673 = true := counterClause1563 (baseVal q)

theorem counterClause1564 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1673 = true := by
  have hs : count1673 q = (countLit q [-117]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-119])
  have hm := merge_left (literal (valuationOf q) (-117)) (literal (valuationOf q) (1673)) (countLit q [-117]) (countLit q [-119]) (count1673 q) 1 (meaningNeg117 q) (meaning1673 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1673 = true := counterClause1564 (baseVal q)

theorem counterClause1565 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 119 = true ∨ valuationOf q 1674 = true := by
  have hs : count1673 q = (countLit q [-117]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-119])
  have hm := merge_two (literal (valuationOf q) (-117)) (literal (valuationOf q) (-119)) (literal (valuationOf q) (1674)) (countLit q [-117]) (countLit q [-119]) (count1673 q) 1 1 (meaningNeg117 q) (meaningNeg119 q) (meaning1674 q) hs
  change (! (valuationOf q 117)) = false ∨ (! (valuationOf q 119)) = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 119 = true ∨ valuation q 1674 = true := counterClause1565 (baseVal q)

theorem counterClause1566 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1675 = true := by
  have hs : count1675 q = (countLit q [-114, -116]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -119])
  have hm := merge_right (literal (valuationOf q) (1673)) (literal (valuationOf q) (1675)) (countLit q [-114, -116]) (countLit q [-117, -119]) (count1675 q) 1 (meaning1673 q) (meaning1675 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1675 = true := counterClause1566 (baseVal q)

theorem counterClause1567 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1676 = true := by
  have hs : count1675 q = (countLit q [-114, -116]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -119])
  have hm := merge_right (literal (valuationOf q) (1674)) (literal (valuationOf q) (1676)) (countLit q [-114, -116]) (countLit q [-117, -119]) (count1675 q) 2 (meaning1674 q) (meaning1676 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1676 = true := counterClause1567 (baseVal q)

theorem counterClause1568 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1675 = true := by
  have hs : count1675 q = (countLit q [-114, -116]) + (countLit q [-117, -119]) := List.countP_append (p := literal q) (l₁ := [-114, -116]) (l₂ := [-117, -119])
  have hm := merge_left (literal (valuationOf q) (1671)) (literal (valuationOf q) (1675)) (countLit q [-114, -116]) (countLit q [-117, -119]) (count1675 q) 1 (meaning1671 q) (meaning1675 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1675 = true := counterClause1568 (baseVal q)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E004.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112004
