import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1660 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1660)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 7 1 (meaning1585 q) (meaning1638 q) (meaning1660 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1638 = false ∨ valuation q 1660 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1661 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1661)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 7 2 (meaning1585 q) (meaning1639 q) (meaning1661 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1639 = false ∨ valuation q 1661 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1662 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1662)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 7 3 (meaning1585 q) (meaning1640 q) (meaning1662 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1640 = false ∨ valuation q 1662 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1663 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1663)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 7 4 (meaning1585 q) (meaning1641 q) (meaning1663 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1641 = false ∨ valuation q 1663 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1664 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1664)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 7 5 (meaning1585 q) (meaning1642 q) (meaning1664 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1642 = false ∨ valuation q 1664 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1660 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1586)) (literal (valuationOf q) (1660)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 8 (meaning1586 q) (meaning1660 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1660 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1661 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1661)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 8 1 (meaning1586 q) (meaning1638 q) (meaning1661 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1638 = false ∨ valuation q 1661 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1662 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1662)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 8 2 (meaning1586 q) (meaning1639 q) (meaning1662 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1639 = false ∨ valuation q 1662 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1663 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1663)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 8 3 (meaning1586 q) (meaning1640 q) (meaning1663 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1640 = false ∨ valuation q 1663 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1664 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1664)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 8 4 (meaning1586 q) (meaning1641 q) (meaning1664 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1641 = false ∨ valuation q 1664 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1661 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1587)) (literal (valuationOf q) (1661)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 9 (meaning1587 q) (meaning1661 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1661 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1662 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1662)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 9 1 (meaning1587 q) (meaning1638 q) (meaning1662 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1638 = false ∨ valuation q 1662 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1663 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1663)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 9 2 (meaning1587 q) (meaning1639 q) (meaning1663 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1639 = false ∨ valuation q 1663 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1664 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1664)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 9 3 (meaning1587 q) (meaning1640 q) (meaning1664 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1640 = false ∨ valuation q 1664 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1662 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1588)) (literal (valuationOf q) (1662)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 10 (meaning1588 q) (meaning1662 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1662 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1663 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1663)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 10 1 (meaning1588 q) (meaning1638 q) (meaning1663 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1638 = false ∨ valuation q 1663 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1664 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1664)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 10 2 (meaning1588 q) (meaning1639 q) (meaning1664 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1639 = false ∨ valuation q 1664 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1665 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1665)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 10 3 (meaning1588 q) (meaning1640 q) (meaning1665 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1640 = false ∨ valuation q 1665 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1663 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1589)) (literal (valuationOf q) (1663)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 11 (meaning1589 q) (meaning1663 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1663 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1664 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1664)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 11 1 (meaning1589 q) (meaning1638 q) (meaning1664 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1638 = false ∨ valuation q 1664 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1690 = true := by
  have hs : count1672 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) + (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (l₂ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1672 q) 6 13 (meaning1521 q) (meaning1665 q) (meaning1690 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1665 = false ∨ valuation q 1690 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1690 = true := by
  have hs : count1672 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) + (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (l₂ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1672 q) 7 12 (meaning1522 q) (meaning1664 q) (meaning1690 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1664 = false ∨ valuation q 1690 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1690 = true := by
  have hs : count1672 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) + (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (l₂ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1672 q) 8 11 (meaning1523 q) (meaning1663 q) (meaning1690 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1663 = false ∨ valuation q 1690 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1690 = true := by
  have hs : count1672 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) + (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (l₂ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1672 q) 9 10 (meaning1524 q) (meaning1662 q) (meaning1690 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1662 = false ∨ valuation q 1690 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1690 = true := by
  have hs : count1672 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) + (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (l₂ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1672 q) 10 9 (meaning1525 q) (meaning1661 q) (meaning1690 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1661 = false ∨ valuation q 1690 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1690 = true := by
  have hs : count1672 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) + (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (l₂ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1672 q) 11 8 (meaning1526 q) (meaning1660 q) (meaning1690 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1660 = false ∨ valuation q 1690 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1690 = true := by
  have hs : count1672 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) + (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (l₂ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1672 q) 12 7 (meaning1527 q) (meaning1659 q) (meaning1690 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1659 = false ∨ valuation q 1690 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1690 = true := by
  have hs : count1672 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) + (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (l₂ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1672 q) 13 6 (meaning1528 q) (meaning1658 q) (meaning1690 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1658 = false ∨ valuation q 1690 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1690 = true := by
  have hs : count1672 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) + (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (l₂ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1672 q) 14 5 (meaning1529 q) (meaning1657 q) (meaning1690 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1657 = false ∨ valuation q 1690 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1690 = true := by
  have hs : count1672 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) + (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (l₂ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1690)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26, -27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86, -89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1672 q) 15 4 (meaning1530 q) (meaning1656 q) (meaning1690 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1656 = false ∨ valuation q 1690 = true := counterClause1374 (baseVal q)

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false := by
  rw [value1690]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1672 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false := by
  rw [value4, value5, value6, value7]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (72 : Vertex) (73 : Vertex) (74 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E064.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112064
