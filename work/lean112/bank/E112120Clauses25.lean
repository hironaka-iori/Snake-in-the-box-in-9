import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1649 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1649)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 5 6 (meaning1570 q) (meaning1629 q) (meaning1649 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1629 = false ∨ valuation q 1649 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1650 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1650)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 5 7 (meaning1570 q) (meaning1630 q) (meaning1650 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1630 = false ∨ valuation q 1650 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1647 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1647)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 6 3 (meaning1571 q) (meaning1626 q) (meaning1647 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1626 = false ∨ valuation q 1647 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1648 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1648)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 6 4 (meaning1571 q) (meaning1627 q) (meaning1648 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1627 = false ∨ valuation q 1648 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1649 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1649)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 6 5 (meaning1571 q) (meaning1628 q) (meaning1649 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1628 = false ∨ valuation q 1649 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1650 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1650)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 6 6 (meaning1571 q) (meaning1629 q) (meaning1650 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1629 = false ∨ valuation q 1650 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1651 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1651)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 6 7 (meaning1571 q) (meaning1630 q) (meaning1651 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1630 = false ∨ valuation q 1651 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1648 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1648)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 7 3 (meaning1572 q) (meaning1626 q) (meaning1648 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1626 = false ∨ valuation q 1648 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1649 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1649)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 7 4 (meaning1572 q) (meaning1627 q) (meaning1649 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1627 = false ∨ valuation q 1649 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1650 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1650)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 7 5 (meaning1572 q) (meaning1628 q) (meaning1650 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1628 = false ∨ valuation q 1650 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1648 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1648)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 8 2 (meaning1573 q) (meaning1625 q) (meaning1648 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1625 = false ∨ valuation q 1648 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1649 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1649)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 8 3 (meaning1573 q) (meaning1626 q) (meaning1649 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1626 = false ∨ valuation q 1649 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1650 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1650)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 8 4 (meaning1573 q) (meaning1627 q) (meaning1650 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1627 = false ∨ valuation q 1650 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1649 = true := by
  have hs : count1639 q = (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) + (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (l₂ := [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1649)) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]) (countLit q [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1639 q) 9 2 (meaning1574 q) (meaning1625 q) (meaning1649 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1625 = false ∨ valuation q 1649 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) + (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (l₂ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1672)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1656 q) 4 13 (meaning1512 q) (meaning1651 q) (meaning1672 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1651 = false ∨ valuation q 1672 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) + (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (l₂ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1672)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1656 q) 5 12 (meaning1513 q) (meaning1650 q) (meaning1672 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1650 = false ∨ valuation q 1672 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) + (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (l₂ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1672)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1656 q) 6 11 (meaning1514 q) (meaning1649 q) (meaning1672 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1649 = false ∨ valuation q 1672 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) + (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (l₂ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1672)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1656 q) 7 10 (meaning1515 q) (meaning1648 q) (meaning1672 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1648 = false ∨ valuation q 1672 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) + (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (l₂ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1672)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1656 q) 8 9 (meaning1516 q) (meaning1647 q) (meaning1672 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1647 = false ∨ valuation q 1672 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) + (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (l₂ := [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1672)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (countLit q [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]) (count1656 q) 9 8 (meaning1517 q) (meaning1646 q) (meaning1672 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1646 = false ∨ valuation q 1672 = true := counterClause820 (baseVal q)

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false := by
  rw [value1672]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1656 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 82 = false ∨ valuation q 94 = false := by
  rw [value14, value22, value82, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (137 : Vertex) (153 : Vertex) (393 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 34 = false := by
  rw [value29, value30, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (197 : Vertex) (199 : Vertex) (205 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 44 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value43, value44, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (259 : Vertex) (386 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value45, value46, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (276 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 84 = false ∨ valuation q 86 = false := by
  rw [value50, value51, value84, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (268 : Vertex) (270 : Vertex) (396 : Vertex) (398 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 72 = false ∨ valuation q 75 = false := by
  rw [value69, value71, value72, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (338 : Vertex) (342 : Vertex) (346 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 79 = false ∨ valuation q 89 = false ∨ valuation q 91 = false := by
  rw [value77, value79, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (385 : Vertex) (387 : Vertex) (401 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value78, value79, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (386 : Vertex) (387 : Vertex) (450 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 87 = false := by
  rw [value80, value81, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (389 : Vertex) (391 : Vertex) (397 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value84, value86, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (396 : Vertex) (398 : Vertex) (460 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value88, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (400 : Vertex) (401 : Vertex) (402 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E120.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112120
