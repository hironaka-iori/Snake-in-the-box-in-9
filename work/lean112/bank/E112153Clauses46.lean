import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1717 = true := by
  have hs : count1717 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1717)) (countLit q [-101]) (countLit q [-102]) (count1717 q) 1 (meaningNeg101 q) (meaning1717 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1717 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1719)) (countLit q [-104]) (countLit q [-106]) (count1719 q) 1 (meaningNeg106 q) (meaning1719 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1719 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1719)) (countLit q [-104]) (countLit q [-106]) (count1719 q) 1 (meaningNeg104 q) (meaning1719 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1719 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1722 = true := by
  have hs : count1721 q = (countLit q [-101, -102]) + (countLit q [-104, -106]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-104, -106])
  have hm := merge_two (literal (valuationOf q) (1717)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1722)) (countLit q [-101, -102]) (countLit q [-104, -106]) (count1721 q) 1 1 (meaning1717 q) (meaning1719 q) (meaning1722 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1719 = false ∨ valuation q 1722 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1728 = true := by
  have hs : count1725 q = (countLit q [-92, -95, -97, -98]) + (countLit q [-101, -102, -104, -106]) := List.countP_append (p := literal q) (l₁ := [-92, -95, -97, -98]) (l₂ := [-101, -102, -104, -106])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1728)) (countLit q [-92, -95, -97, -98]) (countLit q [-101, -102, -104, -106]) (count1725 q) 2 2 (meaning1714 q) (meaning1722 q) (meaning1728 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1722 = false ∨ valuation q 1728 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_right (literal (valuationOf q) (-110)) (literal (valuationOf q) (1733)) (countLit q [-109]) (countLit q [-110]) (count1733 q) 1 (meaningNeg110 q) (meaning1733 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1733 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-109)) (literal (valuationOf q) (1733)) (countLit q [-109]) (countLit q [-110]) (count1733 q) 1 (meaningNeg109 q) (meaning1733 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1733 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_left (literal (valuationOf q) (-114)) (literal (valuationOf q) (1735)) (countLit q [-114]) (countLit q [-116]) (count1735 q) 1 (meaningNeg114 q) (meaning1735 q) hs
  change (! (valuationOf q 114)) = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 1735 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 114 = true ∨ valuationOf q 116 = true ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-114]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-114]) (l₂ := [-116])
  have hm := merge_two (literal (valuationOf q) (-114)) (literal (valuationOf q) (-116)) (literal (valuationOf q) (1736)) (countLit q [-114]) (countLit q [-116]) (count1735 q) 1 1 (meaningNeg114 q) (meaningNeg116 q) (meaning1736 q) hs
  change (! (valuationOf q 114)) = false ∨ (! (valuationOf q 116)) = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 114 = true ∨ valuation q 116 = true ∨ valuation q 1736 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1737 = true := by
  have hs : count1737 q = (countLit q [-109, -110]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-114, -116])
  have hm := merge_right (literal (valuationOf q) (1735)) (literal (valuationOf q) (1737)) (countLit q [-109, -110]) (countLit q [-114, -116]) (count1737 q) 1 (meaning1735 q) (meaning1737 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1737 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1738 = true := by
  have hs : count1737 q = (countLit q [-109, -110]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-114, -116])
  have hm := merge_right (literal (valuationOf q) (1736)) (literal (valuationOf q) (1738)) (countLit q [-109, -110]) (countLit q [-114, -116]) (count1737 q) 2 (meaning1736 q) (meaning1738 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1738 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1738 = true := by
  have hs : count1737 q = (countLit q [-109, -110]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-114, -116])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1738)) (countLit q [-109, -110]) (countLit q [-114, -116]) (count1737 q) 1 1 (meaning1733 q) (meaning1735 q) (meaning1738 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1735 = false ∨ valuation q 1738 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1739 = true := by
  have hs : count1737 q = (countLit q [-109, -110]) + (countLit q [-114, -116]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-114, -116])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1739)) (countLit q [-109, -110]) (countLit q [-114, -116]) (count1737 q) 1 2 (meaning1733 q) (meaning1736 q) (meaning1739 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1736 = false ∨ valuation q 1739 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 1741 = true := by
  have hs : count1741 q = (countLit q [-119]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-119]) (l₂ := [-120])
  have hm := merge_right (literal (valuationOf q) (-120)) (literal (valuationOf q) (1741)) (countLit q [-119]) (countLit q [-120]) (count1741 q) 1 (meaningNeg120 q) (meaning1741 q) hs
  change (! (valuationOf q 120)) = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 1741 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 1741 = true := by
  have hs : count1741 q = (countLit q [-119]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-119]) (l₂ := [-120])
  have hm := merge_left (literal (valuationOf q) (-119)) (literal (valuationOf q) (1741)) (countLit q [-119]) (countLit q [-120]) (count1741 q) 1 (meaningNeg119 q) (meaning1741 q) hs
  change (! (valuationOf q 119)) = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 1741 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 124 = true ∨ valuationOf q 1743 = true := by
  have hs : count1743 q = (countLit q [-122]) + (countLit q [-124]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-124])
  have hm := merge_right (literal (valuationOf q) (-124)) (literal (valuationOf q) (1743)) (countLit q [-122]) (countLit q [-124]) (count1743 q) 1 (meaningNeg124 q) (meaning1743 q) hs
  change (! (valuationOf q 124)) = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 124 = true ∨ valuation q 1743 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 122 = true ∨ valuationOf q 1743 = true := by
  have hs : count1743 q = (countLit q [-122]) + (countLit q [-124]) := List.countP_append (p := literal q) (l₁ := [-122]) (l₂ := [-124])
  have hm := merge_left (literal (valuationOf q) (-122)) (literal (valuationOf q) (1743)) (countLit q [-122]) (countLit q [-124]) (count1743 q) 1 (meaningNeg122 q) (meaning1743 q) hs
  change (! (valuationOf q 122)) = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 122 = true ∨ valuation q 1743 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 1743 = false ∨ valuationOf q 1745 = true := by
  have hs : count1745 q = (countLit q [-119, -120]) + (countLit q [-122, -124]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-122, -124])
  have hm := merge_right (literal (valuationOf q) (1743)) (literal (valuationOf q) (1745)) (countLit q [-119, -120]) (countLit q [-122, -124]) (count1745 q) 1 (meaning1743 q) (meaning1745 q) hs
  change valuationOf q 1743 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 1743 = false ∨ valuation q 1745 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1745 = true := by
  have hs : count1745 q = (countLit q [-119, -120]) + (countLit q [-122, -124]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-122, -124])
  have hm := merge_left (literal (valuationOf q) (1741)) (literal (valuationOf q) (1745)) (countLit q [-119, -120]) (countLit q [-122, -124]) (count1745 q) 1 (meaning1741 q) (meaning1745 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1745 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1746 = true := by
  have hs : count1745 q = (countLit q [-119, -120]) + (countLit q [-122, -124]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-122, -124])
  have hm := merge_two (literal (valuationOf q) (1741)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1746)) (countLit q [-119, -120]) (countLit q [-122, -124]) (count1745 q) 1 1 (meaning1741 q) (meaning1743 q) (meaning1746 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1743 = false ∨ valuation q 1746 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1751 = true := by
  have hs : count1749 q = (countLit q [-109, -110, -114, -116]) + (countLit q [-119, -120, -122, -124]) := List.countP_append (p := literal q) (l₁ := [-109, -110, -114, -116]) (l₂ := [-119, -120, -122, -124])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1746)) (literal (valuationOf q) (1751)) (countLit q [-109, -110, -114, -116]) (countLit q [-119, -120, -122, -124]) (count1749 q) 1 2 (meaning1737 q) (meaning1746 q) (meaning1751 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1746 = false ∨ valuation q 1751 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1751 = true := by
  have hs : count1749 q = (countLit q [-109, -110, -114, -116]) + (countLit q [-119, -120, -122, -124]) := List.countP_append (p := literal q) (l₁ := [-109, -110, -114, -116]) (l₂ := [-119, -120, -122, -124])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1751)) (countLit q [-109, -110, -114, -116]) (countLit q [-119, -120, -122, -124]) (count1749 q) 2 1 (meaning1738 q) (meaning1745 q) (meaning1751 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1745 = false ∨ valuation q 1751 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1751 = true := by
  have hs : count1749 q = (countLit q [-109, -110, -114, -116]) + (countLit q [-119, -120, -122, -124]) := List.countP_append (p := literal q) (l₁ := [-109, -110, -114, -116]) (l₂ := [-119, -120, -122, -124])
  have hm := merge_left (literal (valuationOf q) (1739)) (literal (valuationOf q) (1751)) (countLit q [-109, -110, -114, -116]) (countLit q [-119, -120, -122, -124]) (count1749 q) 3 (meaning1739 q) (meaning1751 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1751 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1763 = true := by
  have hs : count1757 q = (countLit q [-92, -95, -97, -98, -101, -102, -104, -106]) + (countLit q [-109, -110, -114, -116, -119, -120, -122, -124]) := List.countP_append (p := literal q) (l₁ := [-92, -95, -97, -98, -101, -102, -104, -106]) (l₂ := [-109, -110, -114, -116, -119, -120, -122, -124])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1763)) (countLit q [-92, -95, -97, -98, -101, -102, -104, -106]) (countLit q [-109, -110, -114, -116, -119, -120, -122, -124]) (count1757 q) 4 3 (meaning1728 q) (meaning1751 q) (meaning1763 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1751 = false ∨ valuation q 1763 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-64, -66, -67, -69, -70, -72, -76, -77, -78, -79, -83, -84, -85, -89, -90]) + (countLit q [-92, -95, -97, -98, -101, -102, -104, -106, -109, -110, -114, -116, -119, -120, -122, -124]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -67, -69, -70, -72, -76, -77, -78, -79, -83, -84, -85, -89, -90]) (l₂ := [-92, -95, -97, -98, -101, -102, -104, -106, -109, -110, -114, -116, -119, -120, -122, -124])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1783)) (countLit q [-64, -66, -67, -69, -70, -72, -76, -77, -78, -79, -83, -84, -85, -89, -90]) (countLit q [-92, -95, -97, -98, -101, -102, -104, -106, -109, -110, -114, -116, -119, -120, -122, -124]) (count1773 q) 4 7 (meaning1697 q) (meaning1763 q) (meaning1783 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1763 = false ∨ valuation q 1783 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-2, -6, -7, -9, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -30, -31, -33, -34, -36, -40, -41, -42, -44, -48, -49, -50, -54, -56, -58, -59, -62]) + (countLit q [-64, -66, -67, -69, -70, -72, -76, -77, -78, -79, -83, -84, -85, -89, -90, -92, -95, -97, -98, -101, -102, -104, -106, -109, -110, -114, -116, -119, -120, -122, -124]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -9, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -30, -31, -33, -34, -36, -40, -41, -42, -44, -48, -49, -50, -54, -56, -58, -59, -62]) (l₂ := [-64, -66, -67, -69, -70, -72, -76, -77, -78, -79, -83, -84, -85, -89, -90, -92, -95, -97, -98, -101, -102, -104, -106, -109, -110, -114, -116, -119, -120, -122, -124])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1816)) (countLit q [-2, -6, -7, -9, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -30, -31, -33, -34, -36, -40, -41, -42, -44, -48, -49, -50, -54, -56, -58, -59, -62]) (countLit q [-64, -66, -67, -69, -70, -72, -76, -77, -78, -79, -83, -84, -85, -89, -90, -92, -95, -97, -98, -101, -102, -104, -106, -109, -110, -114, -116, -119, -120, -122, -124]) (count1795 q) 11 11 (meaning1638 q) (meaning1783 q) (meaning1816 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1783 = false ∨ valuation q 1816 = true := counterClause1498 (baseVal q)

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1816 = false := by
  rw [value1816]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1795 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 20 = false := by
  rw [value14, value15, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (133 : Vertex) (140 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 27 = false ∨ valuation q 28 = false := by
  rw [value17, value18, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (138 : Vertex) (139 : Vertex) (154 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value19, value20, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (140 : Vertex) (141 : Vertex) (396 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 32 = false := by
  rw [value29, value30, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (194 : Vertex) (196 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value32, value33, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (198 : Vertex) (199 : Vertex) (206 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E153.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112153
