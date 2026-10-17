import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1646 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1646)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 3 5 (meaning1568 q) (meaning1628 q) (meaning1646 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1628 = false ∨ valuation q 1646 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1647 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1647)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 3 6 (meaning1568 q) (meaning1629 q) (meaning1647 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1629 = false ∨ valuation q 1647 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1645 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1645)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 4 3 (meaning1569 q) (meaning1626 q) (meaning1645 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1626 = false ∨ valuation q 1645 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1646 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1646)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 4 4 (meaning1569 q) (meaning1627 q) (meaning1646 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1627 = false ∨ valuation q 1646 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1647 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1647)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 4 5 (meaning1569 q) (meaning1628 q) (meaning1647 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1628 = false ∨ valuation q 1647 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1648 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1648)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 4 6 (meaning1569 q) (meaning1629 q) (meaning1648 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1629 = false ∨ valuation q 1648 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1645 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1645)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 5 2 (meaning1570 q) (meaning1625 q) (meaning1645 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1625 = false ∨ valuation q 1645 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1646 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1646)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 5 3 (meaning1570 q) (meaning1626 q) (meaning1646 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1626 = false ∨ valuation q 1646 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1647 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1647)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 5 4 (meaning1570 q) (meaning1627 q) (meaning1647 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1627 = false ∨ valuation q 1647 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1648 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1648)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 5 5 (meaning1570 q) (meaning1628 q) (meaning1648 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1628 = false ∨ valuation q 1648 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1649 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1649)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 5 6 (meaning1570 q) (meaning1629 q) (meaning1649 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1629 = false ∨ valuation q 1649 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1647 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1647)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 6 3 (meaning1571 q) (meaning1626 q) (meaning1647 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1626 = false ∨ valuation q 1647 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1648 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1648)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 6 4 (meaning1571 q) (meaning1627 q) (meaning1648 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1627 = false ∨ valuation q 1648 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1649 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1649)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 6 5 (meaning1571 q) (meaning1628 q) (meaning1649 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1628 = false ∨ valuation q 1649 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1648 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1648)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 7 3 (meaning1572 q) (meaning1626 q) (meaning1648 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1626 = false ∨ valuation q 1648 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1649 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1649)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 7 4 (meaning1572 q) (meaning1627 q) (meaning1649 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1627 = false ∨ valuation q 1649 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1650 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1650)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 7 5 (meaning1572 q) (meaning1628 q) (meaning1650 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1628 = false ∨ valuation q 1650 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1648 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1648)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 8 2 (meaning1573 q) (meaning1625 q) (meaning1648 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1625 = false ∨ valuation q 1648 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1649 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1649)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 8 3 (meaning1573 q) (meaning1626 q) (meaning1649 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1626 = false ∨ valuation q 1649 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1650 = true := by
  have hs : count1639 q = (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) + (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (l₂ := [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1650)) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87]) (countLit q [-88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1639 q) 8 4 (meaning1573 q) (meaning1627 q) (meaning1650 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1627 = false ∨ valuation q 1650 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) + (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (l₂ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1672)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1656 q) 5 12 (meaning1513 q) (meaning1650 q) (meaning1672 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1650 = false ∨ valuation q 1672 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) + (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (l₂ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1672)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1656 q) 6 11 (meaning1514 q) (meaning1649 q) (meaning1672 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1649 = false ∨ valuation q 1672 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) + (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (l₂ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1672)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1656 q) 7 10 (meaning1515 q) (meaning1648 q) (meaning1672 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1648 = false ∨ valuation q 1672 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) + (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (l₂ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1672)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1656 q) 8 9 (meaning1516 q) (meaning1647 q) (meaning1672 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1647 = false ∨ valuation q 1672 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) + (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (l₂ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1672)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1656 q) 9 8 (meaning1517 q) (meaning1646 q) (meaning1672 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1646 = false ∨ valuation q 1672 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) + (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (l₂ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1672)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1656 q) 10 7 (meaning1518 q) (meaning1645 q) (meaning1672 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1645 = false ∨ valuation q 1672 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) + (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (l₂ := [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1672)) (countLit q [-2, -5, -6, -10, -11, -13, -15, -18, -20, -22, -23, -24, -27, -30, -33, -34, -35, -37, -39, -42, -43, -46, -48, -49, -51, -52, -56, -57]) (countLit q [-58, -59, -62, -66, -67, -70, -72, -74, -75, -77, -79, -82, -85, -87, -88, -90, -94, -95, -96, -97, -101, -103, -104, -106, -107, -111, -112, -113, -114]) (count1656 q) 11 6 (meaning1519 q) (meaning1644 q) (meaning1672 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1644 = false ∨ valuation q 1672 = true := counterClause667 (baseVal q)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false := by
  rw [value1672]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1656 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 27 = false ∨ valuation q 62 = false ∨ valuation q 100 = false := by
  rw [value1, value27, value62, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (96 : Vertex) (224 : Vertex) (352 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 71 = false ∨ valuation q 74 = false := by
  rw [value5, value7, value71, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (107 : Vertex) (111 : Vertex) (363 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value29, value30, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (230 : Vertex) (236 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value45, value46, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (289 : Vertex) (296 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E058.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112058
