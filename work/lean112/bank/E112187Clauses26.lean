import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1610 = true := by
  have hs : count1607 q = (countLit q [-80, -84]) + (countLit q [-85, -88]) := List.countP_append (p := literal q) (l₁ := [-80, -84]) (l₂ := [-85, -88])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1610)) (countLit q [-80, -84]) (countLit q [-85, -88]) (count1607 q) 2 2 (meaning1604 q) (meaning1606 q) (meaning1610 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1606 = false ∨ valuation q 1610 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1611 = true := by
  have hs : count1611 q = (countLit q [-74, -75, -78]) + (countLit q [-80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78]) (l₂ := [-80, -84, -85, -88])
  have hm := merge_right (literal (valuationOf q) (1607)) (literal (valuationOf q) (1611)) (countLit q [-74, -75, -78]) (countLit q [-80, -84, -85, -88]) (count1611 q) 1 (meaning1607 q) (meaning1611 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1611 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1612 = true := by
  have hs : count1611 q = (countLit q [-74, -75, -78]) + (countLit q [-80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78]) (l₂ := [-80, -84, -85, -88])
  have hm := merge_right (literal (valuationOf q) (1608)) (literal (valuationOf q) (1612)) (countLit q [-74, -75, -78]) (countLit q [-80, -84, -85, -88]) (count1611 q) 2 (meaning1608 q) (meaning1612 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1612 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1613 = true := by
  have hs : count1611 q = (countLit q [-74, -75, -78]) + (countLit q [-80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78]) (l₂ := [-80, -84, -85, -88])
  have hm := merge_right (literal (valuationOf q) (1609)) (literal (valuationOf q) (1613)) (countLit q [-74, -75, -78]) (countLit q [-80, -84, -85, -88]) (count1611 q) 3 (meaning1609 q) (meaning1613 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1613 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1614 = true := by
  have hs : count1611 q = (countLit q [-74, -75, -78]) + (countLit q [-80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78]) (l₂ := [-80, -84, -85, -88])
  have hm := merge_right (literal (valuationOf q) (1610)) (literal (valuationOf q) (1614)) (countLit q [-74, -75, -78]) (countLit q [-80, -84, -85, -88]) (count1611 q) 4 (meaning1610 q) (meaning1614 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1614 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1611 = true := by
  have hs : count1611 q = (countLit q [-74, -75, -78]) + (countLit q [-80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78]) (l₂ := [-80, -84, -85, -88])
  have hm := merge_left (literal (valuationOf q) (1600)) (literal (valuationOf q) (1611)) (countLit q [-74, -75, -78]) (countLit q [-80, -84, -85, -88]) (count1611 q) 1 (meaning1600 q) (meaning1611 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1611 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1612 = true := by
  have hs : count1611 q = (countLit q [-74, -75, -78]) + (countLit q [-80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78]) (l₂ := [-80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1612)) (countLit q [-74, -75, -78]) (countLit q [-80, -84, -85, -88]) (count1611 q) 1 1 (meaning1600 q) (meaning1607 q) (meaning1612 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1607 = false ∨ valuation q 1612 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1613 = true := by
  have hs : count1611 q = (countLit q [-74, -75, -78]) + (countLit q [-80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78]) (l₂ := [-80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1613)) (countLit q [-74, -75, -78]) (countLit q [-80, -84, -85, -88]) (count1611 q) 1 2 (meaning1600 q) (meaning1608 q) (meaning1613 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1608 = false ∨ valuation q 1613 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1614 = true := by
  have hs : count1611 q = (countLit q [-74, -75, -78]) + (countLit q [-80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78]) (l₂ := [-80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1614)) (countLit q [-74, -75, -78]) (countLit q [-80, -84, -85, -88]) (count1611 q) 1 3 (meaning1600 q) (meaning1609 q) (meaning1614 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1609 = false ∨ valuation q 1614 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1612 = true := by
  have hs : count1611 q = (countLit q [-74, -75, -78]) + (countLit q [-80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78]) (l₂ := [-80, -84, -85, -88])
  have hm := merge_left (literal (valuationOf q) (1601)) (literal (valuationOf q) (1612)) (countLit q [-74, -75, -78]) (countLit q [-80, -84, -85, -88]) (count1611 q) 2 (meaning1601 q) (meaning1612 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1612 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1613 = true := by
  have hs : count1611 q = (countLit q [-74, -75, -78]) + (countLit q [-80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78]) (l₂ := [-80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1613)) (countLit q [-74, -75, -78]) (countLit q [-80, -84, -85, -88]) (count1611 q) 2 1 (meaning1601 q) (meaning1607 q) (meaning1613 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1607 = false ∨ valuation q 1613 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1614 = true := by
  have hs : count1611 q = (countLit q [-74, -75, -78]) + (countLit q [-80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78]) (l₂ := [-80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1614)) (countLit q [-74, -75, -78]) (countLit q [-80, -84, -85, -88]) (count1611 q) 2 2 (meaning1601 q) (meaning1608 q) (meaning1614 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1608 = false ∨ valuation q 1614 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1615 = true := by
  have hs : count1611 q = (countLit q [-74, -75, -78]) + (countLit q [-80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78]) (l₂ := [-80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1615)) (countLit q [-74, -75, -78]) (countLit q [-80, -84, -85, -88]) (count1611 q) 2 3 (meaning1601 q) (meaning1609 q) (meaning1615 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1609 = false ∨ valuation q 1615 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1615 = true := by
  have hs : count1611 q = (countLit q [-74, -75, -78]) + (countLit q [-80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-74, -75, -78]) (l₂ := [-80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1615)) (countLit q [-74, -75, -78]) (countLit q [-80, -84, -85, -88]) (count1611 q) 3 2 (meaning1602 q) (meaning1608 q) (meaning1615 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1608 = false ∨ valuation q 1615 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1619 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1619)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 1 1 (meaning1591 q) (meaning1611 q) (meaning1619 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1611 = false ∨ valuation q 1619 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1620 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1620)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 1 2 (meaning1591 q) (meaning1612 q) (meaning1620 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1612 = false ∨ valuation q 1620 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1621 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1621)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 1 3 (meaning1591 q) (meaning1613 q) (meaning1621 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1613 = false ∨ valuation q 1621 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1622 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1622)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 1 4 (meaning1591 q) (meaning1614 q) (meaning1622 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1614 = false ∨ valuation q 1622 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1623 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1623)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 1 5 (meaning1591 q) (meaning1615 q) (meaning1623 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1615 = false ∨ valuation q 1623 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1619 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_left (literal (valuationOf q) (1592)) (literal (valuationOf q) (1619)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 2 (meaning1592 q) (meaning1619 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1619 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1620 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1620)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 2 1 (meaning1592 q) (meaning1611 q) (meaning1620 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1611 = false ∨ valuation q 1620 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1621 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1621)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 2 2 (meaning1592 q) (meaning1612 q) (meaning1621 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1612 = false ∨ valuation q 1621 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1622 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1622)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 2 3 (meaning1592 q) (meaning1613 q) (meaning1622 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1613 = false ∨ valuation q 1622 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1623 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1623)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 2 4 (meaning1592 q) (meaning1614 q) (meaning1623 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1614 = false ∨ valuation q 1623 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1621 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1621)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 3 1 (meaning1593 q) (meaning1611 q) (meaning1621 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1611 = false ∨ valuation q 1621 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1622 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1622)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 3 2 (meaning1593 q) (meaning1612 q) (meaning1622 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1612 = false ∨ valuation q 1622 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1623 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1623)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 3 3 (meaning1593 q) (meaning1613 q) (meaning1623 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1613 = false ∨ valuation q 1623 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1624 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1624)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 3 4 (meaning1593 q) (meaning1614 q) (meaning1624 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1614 = false ∨ valuation q 1624 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1625 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1625)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 3 5 (meaning1593 q) (meaning1615 q) (meaning1625 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1615 = false ∨ valuation q 1625 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1622 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1622)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 4 1 (meaning1594 q) (meaning1611 q) (meaning1622 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1611 = false ∨ valuation q 1622 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1623 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1623)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 4 2 (meaning1594 q) (meaning1612 q) (meaning1623 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1612 = false ∨ valuation q 1623 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1624 = true := by
  have hs : count1618 q = (countLit q [-60, -65, -66, -68, -69, -70, -72]) + (countLit q [-74, -75, -78, -80, -84, -85, -88]) := List.countP_append (p := literal q) (l₁ := [-60, -65, -66, -68, -69, -70, -72]) (l₂ := [-74, -75, -78, -80, -84, -85, -88])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1624)) (countLit q [-60, -65, -66, -68, -69, -70, -72]) (countLit q [-74, -75, -78, -80, -84, -85, -88]) (count1618 q) 4 3 (meaning1594 q) (meaning1613 q) (meaning1624 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1613 = false ∨ valuation q 1624 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E187.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112187
