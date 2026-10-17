import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -104, -106]) + (countLit q [-109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -104, -106]) (l₂ := [-109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1619)) (countLit q [-102, -103, -104, -106]) (countLit q [-109, -112, -113, -115]) (count1616 q) 1 3 (meaning1604 q) (meaning1614 q) (meaning1619 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1614 = false ∨ valuation q 1619 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -104, -106]) + (countLit q [-109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -104, -106]) (l₂ := [-109, -112, -113, -115])
  have hm := merge_left (literal (valuationOf q) (1605)) (literal (valuationOf q) (1617)) (countLit q [-102, -103, -104, -106]) (countLit q [-109, -112, -113, -115]) (count1616 q) 2 (meaning1605 q) (meaning1617 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1617 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -104, -106]) + (countLit q [-109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -104, -106]) (l₂ := [-109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1618)) (countLit q [-102, -103, -104, -106]) (countLit q [-109, -112, -113, -115]) (count1616 q) 2 1 (meaning1605 q) (meaning1612 q) (meaning1618 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1612 = false ∨ valuation q 1618 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -104, -106]) + (countLit q [-109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -104, -106]) (l₂ := [-109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1619)) (countLit q [-102, -103, -104, -106]) (countLit q [-109, -112, -113, -115]) (count1616 q) 2 2 (meaning1605 q) (meaning1613 q) (meaning1619 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1613 = false ∨ valuation q 1619 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -104, -106]) + (countLit q [-109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -104, -106]) (l₂ := [-109, -112, -113, -115])
  have hm := merge_left (literal (valuationOf q) (1606)) (literal (valuationOf q) (1618)) (countLit q [-102, -103, -104, -106]) (countLit q [-109, -112, -113, -115]) (count1616 q) 3 (meaning1606 q) (meaning1618 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1618 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-102, -103, -104, -106]) + (countLit q [-109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-102, -103, -104, -106]) (l₂ := [-109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1619)) (countLit q [-102, -103, -104, -106]) (countLit q [-109, -112, -113, -115]) (count1616 q) 3 1 (meaning1606 q) (meaning1612 q) (meaning1619 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1612 = false ∨ valuation q 1619 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1625 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_right (literal (valuationOf q) (1617)) (literal (valuationOf q) (1625)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 2 (meaning1617 q) (meaning1625 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1625 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1625 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1625)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 1 1 (meaning1593 q) (meaning1616 q) (meaning1625 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1616 = false ∨ valuation q 1625 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1626 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1626)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 1 2 (meaning1593 q) (meaning1617 q) (meaning1626 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1617 = false ∨ valuation q 1626 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1625 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_left (literal (valuationOf q) (1594)) (literal (valuationOf q) (1625)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 2 (meaning1594 q) (meaning1625 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1625 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1626 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1626)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 2 1 (meaning1594 q) (meaning1616 q) (meaning1626 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1616 = false ∨ valuation q 1626 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1627 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1627)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 2 2 (meaning1594 q) (meaning1617 q) (meaning1627 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1617 = false ∨ valuation q 1627 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1628)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 2 3 (meaning1594 q) (meaning1618 q) (meaning1628 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1618 = false ∨ valuation q 1628 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1629)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 2 4 (meaning1594 q) (meaning1619 q) (meaning1629 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1619 = false ∨ valuation q 1629 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1627 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1627)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 3 1 (meaning1595 q) (meaning1616 q) (meaning1627 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1616 = false ∨ valuation q 1627 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1628)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 3 2 (meaning1595 q) (meaning1617 q) (meaning1628 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1617 = false ∨ valuation q 1628 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1629)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 3 3 (meaning1595 q) (meaning1618 q) (meaning1629 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1618 = false ∨ valuation q 1629 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1630 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1630)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 3 4 (meaning1595 q) (meaning1619 q) (meaning1630 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1619 = false ∨ valuation q 1630 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1628)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 4 1 (meaning1596 q) (meaning1616 q) (meaning1628 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1616 = false ∨ valuation q 1628 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1629)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 4 2 (meaning1596 q) (meaning1617 q) (meaning1629 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1617 = false ∨ valuation q 1629 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1630 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1630)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 4 3 (meaning1596 q) (meaning1618 q) (meaning1630 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1618 = false ∨ valuation q 1630 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1629)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 5 1 (meaning1597 q) (meaning1616 q) (meaning1629 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1616 = false ∨ valuation q 1629 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1630 = true := by
  have hs : count1624 q = (countLit q [-88, -91, -92, -94, -95, -96, -100]) + (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92, -94, -95, -96, -100]) (l₂ := [-102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1630)) (countLit q [-88, -91, -92, -94, -95, -96, -100]) (countLit q [-102, -103, -104, -106, -109, -112, -113, -115]) (count1624 q) 5 2 (meaning1597 q) (meaning1617 q) (meaning1630 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1617 = false ∨ valuation q 1630 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1646 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1646)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 3 5 (meaning1568 q) (meaning1628 q) (meaning1646 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1628 = false ∨ valuation q 1646 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1647 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1647)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 3 6 (meaning1568 q) (meaning1629 q) (meaning1647 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1629 = false ∨ valuation q 1647 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1648 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1648)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 3 7 (meaning1568 q) (meaning1630 q) (meaning1648 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1630 = false ∨ valuation q 1648 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1646 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1646)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 4 4 (meaning1569 q) (meaning1627 q) (meaning1646 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1627 = false ∨ valuation q 1646 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1647 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1647)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 4 5 (meaning1569 q) (meaning1628 q) (meaning1647 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1628 = false ∨ valuation q 1647 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1648 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1648)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 4 6 (meaning1569 q) (meaning1629 q) (meaning1648 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1629 = false ∨ valuation q 1648 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1649 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1649)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 4 7 (meaning1569 q) (meaning1630 q) (meaning1649 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1630 = false ∨ valuation q 1649 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1647 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1647)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 5 4 (meaning1570 q) (meaning1627 q) (meaning1647 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1627 = false ∨ valuation q 1647 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1648 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1648)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 5 5 (meaning1570 q) (meaning1628 q) (meaning1648 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1628 = false ∨ valuation q 1648 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E120.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112120
