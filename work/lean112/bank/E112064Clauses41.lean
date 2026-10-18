import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1639 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1639)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 1 1 (meaning1607 q) (meaning1630 q) (meaning1639 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1630 = false ∨ valuation q 1639 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1640 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1640)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 1 2 (meaning1607 q) (meaning1631 q) (meaning1640 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1631 = false ∨ valuation q 1640 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1641 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1641)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 1 3 (meaning1607 q) (meaning1632 q) (meaning1641 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1632 = false ∨ valuation q 1641 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1639 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1608)) (literal (valuationOf q) (1639)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 2 (meaning1608 q) (meaning1639 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1639 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1640 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1640)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 2 1 (meaning1608 q) (meaning1630 q) (meaning1640 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1630 = false ∨ valuation q 1640 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1641 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1641)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 2 2 (meaning1608 q) (meaning1631 q) (meaning1641 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1631 = false ∨ valuation q 1641 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1640 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1609)) (literal (valuationOf q) (1640)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 3 (meaning1609 q) (meaning1640 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1640 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1641 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1641)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 3 1 (meaning1609 q) (meaning1630 q) (meaning1641 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1630 = false ∨ valuation q 1641 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1641 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1610)) (literal (valuationOf q) (1641)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 4 (meaning1610 q) (meaning1641 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1641 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1642 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1642)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 4 1 (meaning1610 q) (meaning1630 q) (meaning1642 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1630 = false ∨ valuation q 1642 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1643 = true := by
  have hs : count1638 q = (countLit q [-89, -90, -91, -92, -96, -97, -99]) + (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-89, -90, -91, -92, -96, -97, -99]) (l₂ := [-103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1643)) (countLit q [-89, -90, -91, -92, -96, -97, -99]) (countLit q [-103, -104, -105, -106, -110, -113, -114, -116]) (count1638 q) 4 2 (meaning1610 q) (meaning1631 q) (meaning1643 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1631 = false ∨ valuation q 1643 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1659 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1659)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 2 5 (meaning1580 q) (meaning1642 q) (meaning1659 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1642 = false ∨ valuation q 1659 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1657 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1657)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 3 2 (meaning1581 q) (meaning1639 q) (meaning1657 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1639 = false ∨ valuation q 1657 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1658 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1658)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 3 3 (meaning1581 q) (meaning1640 q) (meaning1658 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1640 = false ∨ valuation q 1658 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1656 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1582)) (literal (valuationOf q) (1656)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 4 (meaning1582 q) (meaning1656 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1656 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1657 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1657)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 4 1 (meaning1582 q) (meaning1638 q) (meaning1657 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1638 = false ∨ valuation q 1657 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1658 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1658)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 4 2 (meaning1582 q) (meaning1639 q) (meaning1658 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1639 = false ∨ valuation q 1658 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1659 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1659)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 4 3 (meaning1582 q) (meaning1640 q) (meaning1659 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1640 = false ∨ valuation q 1659 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1657 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1583)) (literal (valuationOf q) (1657)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 5 (meaning1583 q) (meaning1657 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1657 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1658 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1658)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 5 1 (meaning1583 q) (meaning1638 q) (meaning1658 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1638 = false ∨ valuation q 1658 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1659 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1659)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 5 2 (meaning1583 q) (meaning1639 q) (meaning1659 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1639 = false ∨ valuation q 1659 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1660 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1660)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 5 3 (meaning1583 q) (meaning1640 q) (meaning1660 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1640 = false ∨ valuation q 1660 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1661 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1661)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 5 4 (meaning1583 q) (meaning1641 q) (meaning1661 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1641 = false ∨ valuation q 1661 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1662 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1662)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 5 5 (meaning1583 q) (meaning1642 q) (meaning1662 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1642 = false ∨ valuation q 1662 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1663 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1663)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 5 6 (meaning1583 q) (meaning1643 q) (meaning1663 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1643 = false ∨ valuation q 1663 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1658 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1584)) (literal (valuationOf q) (1658)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 6 (meaning1584 q) (meaning1658 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1658 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1659 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1659)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 6 1 (meaning1584 q) (meaning1638 q) (meaning1659 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1638 = false ∨ valuation q 1659 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1660 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1660)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 6 2 (meaning1584 q) (meaning1639 q) (meaning1660 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1639 = false ∨ valuation q 1660 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1661 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1661)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 6 3 (meaning1584 q) (meaning1640 q) (meaning1661 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1640 = false ∨ valuation q 1661 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1662 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1662)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 6 4 (meaning1584 q) (meaning1641 q) (meaning1662 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1641 = false ∨ valuation q 1662 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1663 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1663)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 6 5 (meaning1584 q) (meaning1642 q) (meaning1663 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1642 = false ∨ valuation q 1663 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1659 = true := by
  have hs : count1653 q = (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) + (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (l₂ := [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116])
  have hm := merge_left (literal (valuationOf q) (1585)) (literal (valuationOf q) (1659)) (countLit q [-59, -60, -62, -65, -66, -68, -70, -72, -74, -76, -78, -81, -82, -83, -86]) (countLit q [-89, -90, -91, -92, -96, -97, -99, -103, -104, -105, -106, -110, -113, -114, -116]) (count1653 q) 7 (meaning1585 q) (meaning1659 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1659 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E064.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112064
