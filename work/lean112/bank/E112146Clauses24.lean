import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1589 = true := by
  have hs : count1584 q = (countLit q [-86, -88, -90, -91, -94, -95, -97]) + (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90, -91, -94, -95, -97]) (l₂ := [-99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1589)) (countLit q [-86, -88, -90, -91, -94, -95, -97]) (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) (count1584 q) 4 2 (meaning1556 q) (meaning1577 q) (meaning1589 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1577 = false ∨ valuation q 1589 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1589 = true := by
  have hs : count1584 q = (countLit q [-86, -88, -90, -91, -94, -95, -97]) + (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90, -91, -94, -95, -97]) (l₂ := [-99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1589)) (countLit q [-86, -88, -90, -91, -94, -95, -97]) (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) (count1584 q) 5 1 (meaning1557 q) (meaning1576 q) (meaning1589 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1576 = false ∨ valuation q 1589 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1590 = true := by
  have hs : count1584 q = (countLit q [-86, -88, -90, -91, -94, -95, -97]) + (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90, -91, -94, -95, -97]) (l₂ := [-99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1590)) (countLit q [-86, -88, -90, -91, -94, -95, -97]) (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) (count1584 q) 5 2 (meaning1557 q) (meaning1577 q) (meaning1590 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1577 = false ∨ valuation q 1590 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1590 = true := by
  have hs : count1584 q = (countLit q [-86, -88, -90, -91, -94, -95, -97]) + (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90, -91, -94, -95, -97]) (l₂ := [-99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1590)) (countLit q [-86, -88, -90, -91, -94, -95, -97]) (countLit q [-99, -101, -104, -106, -108, -109, -112, -113]) (count1584 q) 6 1 (meaning1558 q) (meaning1576 q) (meaning1590 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1576 = false ∨ valuation q 1590 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1602 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1602)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 1 3 (meaning1525 q) (meaning1586 q) (meaning1602 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1586 = false ∨ valuation q 1602 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1603 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1603)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 1 4 (meaning1525 q) (meaning1587 q) (meaning1603 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1587 = false ∨ valuation q 1603 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1604 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1604)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 1 5 (meaning1525 q) (meaning1588 q) (meaning1604 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1588 = false ∨ valuation q 1604 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1605 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1605)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 1 6 (meaning1525 q) (meaning1589 q) (meaning1605 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1589 = false ∨ valuation q 1605 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1604 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1604)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 2 4 (meaning1526 q) (meaning1587 q) (meaning1604 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1587 = false ∨ valuation q 1604 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1605 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1605)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 2 5 (meaning1526 q) (meaning1588 q) (meaning1605 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1588 = false ∨ valuation q 1605 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1606 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1606)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 2 6 (meaning1526 q) (meaning1589 q) (meaning1606 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1589 = false ∨ valuation q 1606 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1607 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1607)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 2 7 (meaning1526 q) (meaning1590 q) (meaning1607 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1590 = false ∨ valuation q 1607 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1605 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1605)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 3 4 (meaning1527 q) (meaning1587 q) (meaning1605 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1587 = false ∨ valuation q 1605 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1606 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1606)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 3 5 (meaning1527 q) (meaning1588 q) (meaning1606 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1588 = false ∨ valuation q 1606 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1607 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1607)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 3 6 (meaning1527 q) (meaning1589 q) (meaning1607 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1589 = false ∨ valuation q 1607 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1605 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1605)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 4 3 (meaning1528 q) (meaning1586 q) (meaning1605 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1586 = false ∨ valuation q 1605 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1606 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1606)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 4 4 (meaning1528 q) (meaning1587 q) (meaning1606 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1587 = false ∨ valuation q 1606 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1607 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1607)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 4 5 (meaning1528 q) (meaning1588 q) (meaning1607 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1588 = false ∨ valuation q 1607 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1606 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1606)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 5 3 (meaning1529 q) (meaning1586 q) (meaning1606 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1586 = false ∨ valuation q 1606 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1607 = true := by
  have hs : count1599 q = (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) + (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (l₂ := [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1607)) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]) (countLit q [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1599 q) 5 4 (meaning1529 q) (meaning1587 q) (meaning1607 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1587 = false ∨ valuation q 1607 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1636 = true := by
  have hs : count1618 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) + (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (l₂ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1618 q) 10 9 (meaning1471 q) (meaning1607 q) (meaning1636 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1607 = false ∨ valuation q 1636 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1636 = true := by
  have hs : count1618 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) + (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (l₂ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1618 q) 11 8 (meaning1472 q) (meaning1606 q) (meaning1636 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1606 = false ∨ valuation q 1636 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1636 = true := by
  have hs : count1618 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) + (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (l₂ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1618 q) 12 7 (meaning1473 q) (meaning1605 q) (meaning1636 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1605 = false ∨ valuation q 1636 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1636 = true := by
  have hs : count1618 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) + (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (l₂ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1618 q) 13 6 (meaning1474 q) (meaning1604 q) (meaning1636 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1604 = false ∨ valuation q 1636 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1636 = true := by
  have hs : count1618 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) + (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (l₂ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1618 q) 14 5 (meaning1475 q) (meaning1603 q) (meaning1636 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1603 = false ∨ valuation q 1636 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1636 = true := by
  have hs : count1618 q = (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) + (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (l₂ := [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113])
  have hm := merge_two (literal (valuationOf q) (1476)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]) (countLit q [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]) (count1618 q) 15 4 (meaning1476 q) (meaning1602 q) (meaning1636 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1602 = false ∨ valuation q 1636 = true := counterClause794 (baseVal q)

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false := by
  rw [value1636]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1618 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value1, value2, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (10 : Vertex) (11 : Vertex) (74 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 14 = false ∨ valuation q 34 = false ∨ valuation q 51 = false := by
  rw [value2, value14, value34, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (11 : Vertex) (75 : Vertex) (139 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 16 = false ∨ valuation q 36 = false ∨ valuation q 53 = false := by
  rw [value3, value16, value36, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (13 : Vertex) (77 : Vertex) (141 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 10 = false ∨ valuation q 11 = false := by
  rw [value8, value9, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (65 : Vertex) (67 : Vertex) (69 : Vertex) (71 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 12 = false ∨ valuation q 14 = false := by
  rw [value8, value9, value12, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (65 : Vertex) (67 : Vertex) (73 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E146.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112146
