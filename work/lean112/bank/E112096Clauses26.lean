import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1599)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 3 2 (meaning1566 q) (meaning1588 q) (meaning1599 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1588 = false ∨ valuation q 1599 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1600 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1600)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 3 3 (meaning1566 q) (meaning1589 q) (meaning1600 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1589 = false ∨ valuation q 1600 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1601 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1601)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 3 4 (meaning1566 q) (meaning1590 q) (meaning1601 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1590 = false ∨ valuation q 1601 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1602 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1602)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 3 5 (meaning1566 q) (meaning1591 q) (meaning1602 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1591 = false ∨ valuation q 1602 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1599)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 4 1 (meaning1567 q) (meaning1587 q) (meaning1599 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1587 = false ∨ valuation q 1599 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1600 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1600)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 4 2 (meaning1567 q) (meaning1588 q) (meaning1600 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1588 = false ∨ valuation q 1600 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1601 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1601)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 4 3 (meaning1567 q) (meaning1589 q) (meaning1601 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1589 = false ∨ valuation q 1601 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1602 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -62, -63, -66, -69, -70]) + (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70]) (l₂ := [-72, -73, -77, -78, -80, -81, -85, -86])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1602)) (countLit q [-60, -61, -62, -63, -66, -69, -70]) (countLit q [-72, -73, -77, -78, -80, -81, -85, -86]) (count1595 q) 4 4 (meaning1567 q) (meaning1590 q) (meaning1602 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1590 = false ∨ valuation q 1602 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-90]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92])
  have hm := merge_right (literal (valuationOf q) (-92)) (literal (valuationOf q) (1610)) (countLit q [-90]) (countLit q [-92]) (count1610 q) 1 (meaningNeg92 q) (meaning1610 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1610 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-90]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1610)) (countLit q [-90]) (countLit q [-92]) (count1610 q) 1 (meaningNeg90 q) (meaning1610 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1610 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 92 = true ∨ valuationOf q 1611 = true := by
  have hs : count1610 q = (countLit q [-90]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (-92)) (literal (valuationOf q) (1611)) (countLit q [-90]) (countLit q [-92]) (count1610 q) 1 1 (meaningNeg90 q) (meaningNeg92 q) (meaning1611 q) hs
  change (! (valuationOf q 90)) = false ∨ (! (valuationOf q 92)) = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 92 = true ∨ valuation q 1611 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-88]) + (countLit q [-90, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -92])
  have hm := merge_right (literal (valuationOf q) (1610)) (literal (valuationOf q) (1612)) (countLit q [-88]) (countLit q [-90, -92]) (count1612 q) 1 (meaning1610 q) (meaning1612 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1612 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-88]) + (countLit q [-90, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -92])
  have hm := merge_right (literal (valuationOf q) (1611)) (literal (valuationOf q) (1613)) (countLit q [-88]) (countLit q [-90, -92]) (count1612 q) 2 (meaning1611 q) (meaning1613 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1613 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-88]) + (countLit q [-90, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -92])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1612)) (countLit q [-88]) (countLit q [-90, -92]) (count1612 q) 1 (meaningNeg88 q) (meaning1612 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1612 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-88]) + (countLit q [-90, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -92])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1613)) (countLit q [-88]) (countLit q [-90, -92]) (count1612 q) 1 1 (meaningNeg88 q) (meaning1610 q) (meaning1613 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1610 = false ∨ valuation q 1613 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1611 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-88]) + (countLit q [-90, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90, -92])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1614)) (countLit q [-88]) (countLit q [-90, -92]) (count1612 q) 1 2 (meaningNeg88 q) (meaning1611 q) (meaning1614 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1611 = false ∨ valuation q 1614 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1615 = true := by
  have hs : count1615 q = (countLit q [-93]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1615)) (countLit q [-93]) (countLit q [-96]) (count1615 q) 1 (meaningNeg96 q) (meaning1615 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1615 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1615 = true := by
  have hs : count1615 q = (countLit q [-93]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1615)) (countLit q [-93]) (countLit q [-96]) (count1615 q) 1 (meaningNeg93 q) (meaning1615 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1615 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1616 = true := by
  have hs : count1615 q = (countLit q [-93]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1616)) (countLit q [-93]) (countLit q [-96]) (count1615 q) 1 1 (meaningNeg93 q) (meaningNeg96 q) (meaning1616 q) hs
  change (! (valuationOf q 93)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 96 = true ∨ valuation q 1616 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-99]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1617)) (countLit q [-99]) (countLit q [-102]) (count1617 q) 1 (meaningNeg102 q) (meaning1617 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1617 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-99]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1617)) (countLit q [-99]) (countLit q [-102]) (count1617 q) 1 (meaningNeg99 q) (meaning1617 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1617 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 102 = true ∨ valuationOf q 1618 = true := by
  have hs : count1617 q = (countLit q [-99]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-102])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-102)) (literal (valuationOf q) (1618)) (countLit q [-99]) (countLit q [-102]) (count1617 q) 1 1 (meaningNeg99 q) (meaningNeg102 q) (meaning1618 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 102)) = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 102 = true ∨ valuation q 1618 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-93, -96]) + (countLit q [-99, -102]) := List.countP_append (p := literal q) (l₁ := [-93, -96]) (l₂ := [-99, -102])
  have hm := merge_right (literal (valuationOf q) (1617)) (literal (valuationOf q) (1619)) (countLit q [-93, -96]) (countLit q [-99, -102]) (count1619 q) 1 (meaning1617 q) (meaning1619 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1619 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-93, -96]) + (countLit q [-99, -102]) := List.countP_append (p := literal q) (l₁ := [-93, -96]) (l₂ := [-99, -102])
  have hm := merge_right (literal (valuationOf q) (1618)) (literal (valuationOf q) (1620)) (countLit q [-93, -96]) (countLit q [-99, -102]) (count1619 q) 2 (meaning1618 q) (meaning1620 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1620 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-93, -96]) + (countLit q [-99, -102]) := List.countP_append (p := literal q) (l₁ := [-93, -96]) (l₂ := [-99, -102])
  have hm := merge_left (literal (valuationOf q) (1615)) (literal (valuationOf q) (1619)) (countLit q [-93, -96]) (countLit q [-99, -102]) (count1619 q) 1 (meaning1615 q) (meaning1619 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1619 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-93, -96]) + (countLit q [-99, -102]) := List.countP_append (p := literal q) (l₁ := [-93, -96]) (l₂ := [-99, -102])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1620)) (countLit q [-93, -96]) (countLit q [-99, -102]) (count1619 q) 1 1 (meaning1615 q) (meaning1617 q) (meaning1620 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1617 = false ∨ valuation q 1620 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1621 = true := by
  have hs : count1619 q = (countLit q [-93, -96]) + (countLit q [-99, -102]) := List.countP_append (p := literal q) (l₁ := [-93, -96]) (l₂ := [-99, -102])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1621)) (countLit q [-93, -96]) (countLit q [-99, -102]) (count1619 q) 1 2 (meaning1615 q) (meaning1618 q) (meaning1621 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1618 = false ∨ valuation q 1621 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-93, -96]) + (countLit q [-99, -102]) := List.countP_append (p := literal q) (l₁ := [-93, -96]) (l₂ := [-99, -102])
  have hm := merge_left (literal (valuationOf q) (1616)) (literal (valuationOf q) (1620)) (countLit q [-93, -96]) (countLit q [-99, -102]) (count1619 q) 2 (meaning1616 q) (meaning1620 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1620 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1621 = true := by
  have hs : count1619 q = (countLit q [-93, -96]) + (countLit q [-99, -102]) := List.countP_append (p := literal q) (l₁ := [-93, -96]) (l₂ := [-99, -102])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1621)) (countLit q [-93, -96]) (countLit q [-99, -102]) (count1619 q) 2 1 (meaning1616 q) (meaning1617 q) (meaning1621 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1617 = false ∨ valuation q 1621 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1622 = true := by
  have hs : count1619 q = (countLit q [-93, -96]) + (countLit q [-99, -102]) := List.countP_append (p := literal q) (l₁ := [-93, -96]) (l₂ := [-99, -102])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1622)) (countLit q [-93, -96]) (countLit q [-99, -102]) (count1619 q) 2 2 (meaning1616 q) (meaning1618 q) (meaning1622 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1618 = false ∨ valuation q 1622 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_right (literal (valuationOf q) (1619)) (literal (valuationOf q) (1623)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 1 (meaning1619 q) (meaning1623 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1623 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-88, -90, -92]) + (countLit q [-93, -96, -99, -102]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-93, -96, -99, -102])
  have hm := merge_right (literal (valuationOf q) (1620)) (literal (valuationOf q) (1624)) (countLit q [-88, -90, -92]) (countLit q [-93, -96, -99, -102]) (count1623 q) 2 (meaning1620 q) (meaning1624 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1624 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E096.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112096
