import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1598)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 4 (meaning1590 q) (meaning1598 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1598 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1596 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1596)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 1 1 (meaning1564 q) (meaning1587 q) (meaning1596 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1587 = false ∨ valuation q 1596 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1597 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1597)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 1 2 (meaning1564 q) (meaning1588 q) (meaning1597 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1588 = false ∨ valuation q 1597 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1598)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 1 3 (meaning1564 q) (meaning1589 q) (meaning1598 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1589 = false ∨ valuation q 1598 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1599)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 1 4 (meaning1564 q) (meaning1590 q) (meaning1599 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1590 = false ∨ valuation q 1599 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1596 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1565)) (literal (valuationOf q) (1596)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 2 (meaning1565 q) (meaning1596 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1596 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1597 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1597)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 2 1 (meaning1565 q) (meaning1587 q) (meaning1597 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1587 = false ∨ valuation q 1597 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1598)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 2 2 (meaning1565 q) (meaning1588 q) (meaning1598 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1588 = false ∨ valuation q 1598 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1599)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 2 3 (meaning1565 q) (meaning1589 q) (meaning1599 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1589 = false ∨ valuation q 1599 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1600 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1600)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 2 4 (meaning1565 q) (meaning1590 q) (meaning1600 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1590 = false ∨ valuation q 1600 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1598)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 3 1 (meaning1566 q) (meaning1587 q) (meaning1598 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1587 = false ∨ valuation q 1598 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1599)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 3 2 (meaning1566 q) (meaning1588 q) (meaning1599 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1588 = false ∨ valuation q 1599 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1600 = true := by
  have hs : count1595 q = (countLit q [-59, -60, -63, -65, -67, -69, -72]) + (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72]) (l₂ := [-73, -76, -77, -80, -82, -84, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1600)) (countLit q [-59, -60, -63, -65, -67, -69, -72]) (countLit q [-73, -76, -77, -80, -82, -84, -86, -89]) (count1595 q) 3 3 (meaning1566 q) (meaning1589 q) (meaning1600 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1589 = false ∨ valuation q 1600 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1610)) (countLit q [-93]) (countLit q [-94]) (count1610 q) 1 (meaningNeg94 q) (meaning1610 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1610 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1610)) (countLit q [-93]) (countLit q [-94]) (count1610 q) 1 (meaningNeg93 q) (meaning1610 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1610 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 94 = true ∨ valuationOf q 1611 = true := by
  have hs : count1610 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (1611)) (countLit q [-93]) (countLit q [-94]) (count1610 q) 1 1 (meaningNeg93 q) (meaningNeg94 q) (meaning1611 q) hs
  change (! (valuationOf q 93)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 94 = true ∨ valuation q 1611 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93, -94])
  have hm := merge_right (literal (valuationOf q) (1610)) (literal (valuationOf q) (1612)) (countLit q [-90]) (countLit q [-93, -94]) (count1612 q) 1 (meaning1610 q) (meaning1612 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1612 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93, -94])
  have hm := merge_right (literal (valuationOf q) (1611)) (literal (valuationOf q) (1613)) (countLit q [-90]) (countLit q [-93, -94]) (count1612 q) 2 (meaning1611 q) (meaning1613 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1613 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93, -94])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1612)) (countLit q [-90]) (countLit q [-93, -94]) (count1612 q) 1 (meaningNeg90 q) (meaning1612 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1612 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93, -94])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1613)) (countLit q [-90]) (countLit q [-93, -94]) (count1612 q) 1 1 (meaningNeg90 q) (meaning1610 q) (meaning1613 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1610 = false ∨ valuation q 1613 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1615 = true := by
  have hs : count1615 q = (countLit q [-97]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1615)) (countLit q [-97]) (countLit q [-99]) (count1615 q) 1 (meaningNeg99 q) (meaning1615 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1615 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1615 = true := by
  have hs : count1615 q = (countLit q [-97]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1615)) (countLit q [-97]) (countLit q [-99]) (count1615 q) 1 (meaningNeg97 q) (meaning1615 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1615 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 99 = true ∨ valuationOf q 1616 = true := by
  have hs : count1615 q = (countLit q [-97]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-99)) (literal (valuationOf q) (1616)) (countLit q [-97]) (countLit q [-99]) (count1615 q) 1 1 (meaningNeg97 q) (meaningNeg99 q) (meaning1616 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 99)) = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 99 = true ∨ valuation q 1616 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1617)) (countLit q [-101]) (countLit q [-102]) (count1617 q) 1 (meaningNeg102 q) (meaning1617 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1617 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1617)) (countLit q [-101]) (countLit q [-102]) (count1617 q) 1 (meaningNeg101 q) (meaning1617 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1617 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 102 = true ∨ valuationOf q 1618 = true := by
  have hs : count1617 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_two (literal (valuationOf q) (-101)) (literal (valuationOf q) (-102)) (literal (valuationOf q) (1618)) (countLit q [-101]) (countLit q [-102]) (count1617 q) 1 1 (meaningNeg101 q) (meaningNeg102 q) (meaning1618 q) hs
  change (! (valuationOf q 101)) = false ∨ (! (valuationOf q 102)) = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 102 = true ∨ valuation q 1618 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-97, -99]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-101, -102])
  have hm := merge_right (literal (valuationOf q) (1617)) (literal (valuationOf q) (1619)) (countLit q [-97, -99]) (countLit q [-101, -102]) (count1619 q) 1 (meaning1617 q) (meaning1619 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1619 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-97, -99]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-101, -102])
  have hm := merge_right (literal (valuationOf q) (1618)) (literal (valuationOf q) (1620)) (countLit q [-97, -99]) (countLit q [-101, -102]) (count1619 q) 2 (meaning1618 q) (meaning1620 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1620 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-97, -99]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-101, -102])
  have hm := merge_left (literal (valuationOf q) (1615)) (literal (valuationOf q) (1619)) (countLit q [-97, -99]) (countLit q [-101, -102]) (count1619 q) 1 (meaning1615 q) (meaning1619 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1619 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-97, -99]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-101, -102])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1620)) (countLit q [-97, -99]) (countLit q [-101, -102]) (count1619 q) 1 1 (meaning1615 q) (meaning1617 q) (meaning1620 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1617 = false ∨ valuation q 1620 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1621 = true := by
  have hs : count1619 q = (countLit q [-97, -99]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-101, -102])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1621)) (countLit q [-97, -99]) (countLit q [-101, -102]) (count1619 q) 1 2 (meaning1615 q) (meaning1618 q) (meaning1621 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1618 = false ∨ valuation q 1621 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-97, -99]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-97, -99]) (l₂ := [-101, -102])
  have hm := merge_left (literal (valuationOf q) (1616)) (literal (valuationOf q) (1620)) (countLit q [-97, -99]) (countLit q [-101, -102]) (count1619 q) 2 (meaning1616 q) (meaning1620 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1620 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E104.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112104
