import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1642 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1642)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 3 5 (meaning1563 q) (meaning1624 q) (meaning1642 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1624 = false ∨ valuation q 1642 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1643 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1643)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 3 6 (meaning1563 q) (meaning1625 q) (meaning1643 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1625 = false ∨ valuation q 1643 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1644 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1644)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 3 7 (meaning1563 q) (meaning1626 q) (meaning1644 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1626 = false ∨ valuation q 1644 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1640 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1640)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 4 2 (meaning1564 q) (meaning1621 q) (meaning1640 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1621 = false ∨ valuation q 1640 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1641 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1641)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 4 3 (meaning1564 q) (meaning1622 q) (meaning1641 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1622 = false ∨ valuation q 1641 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1642 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1642)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 4 4 (meaning1564 q) (meaning1623 q) (meaning1642 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1623 = false ∨ valuation q 1642 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1643 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1643)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 4 5 (meaning1564 q) (meaning1624 q) (meaning1643 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1624 = false ∨ valuation q 1643 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1644 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1644)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 4 6 (meaning1564 q) (meaning1625 q) (meaning1644 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1625 = false ∨ valuation q 1644 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1645 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1645)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 4 7 (meaning1564 q) (meaning1626 q) (meaning1645 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1626 = false ∨ valuation q 1645 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1641 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1641)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 5 2 (meaning1565 q) (meaning1621 q) (meaning1641 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1621 = false ∨ valuation q 1641 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1642 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1642)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 5 3 (meaning1565 q) (meaning1622 q) (meaning1642 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1622 = false ∨ valuation q 1642 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1643 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1643)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 5 4 (meaning1565 q) (meaning1623 q) (meaning1643 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1623 = false ∨ valuation q 1643 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1644 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1644)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 5 5 (meaning1565 q) (meaning1624 q) (meaning1644 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1624 = false ∨ valuation q 1644 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1645 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1645)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 5 6 (meaning1565 q) (meaning1625 q) (meaning1645 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1625 = false ∨ valuation q 1645 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1646 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1646)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 5 7 (meaning1565 q) (meaning1626 q) (meaning1646 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1626 = false ∨ valuation q 1646 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1641 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1641)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 6 1 (meaning1566 q) (meaning1620 q) (meaning1641 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1620 = false ∨ valuation q 1641 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1642 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1642)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 6 2 (meaning1566 q) (meaning1621 q) (meaning1642 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1621 = false ∨ valuation q 1642 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1643 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1643)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 6 3 (meaning1566 q) (meaning1622 q) (meaning1643 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1622 = false ∨ valuation q 1643 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1644 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1644)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 6 4 (meaning1566 q) (meaning1623 q) (meaning1644 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1623 = false ∨ valuation q 1644 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1645 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1645)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 6 5 (meaning1566 q) (meaning1624 q) (meaning1645 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1624 = false ∨ valuation q 1645 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1646 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1646)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 6 6 (meaning1566 q) (meaning1625 q) (meaning1646 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1625 = false ∨ valuation q 1646 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1642 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1642)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 7 1 (meaning1567 q) (meaning1620 q) (meaning1642 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1620 = false ∨ valuation q 1642 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1643 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1643)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 7 2 (meaning1567 q) (meaning1621 q) (meaning1643 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1621 = false ∨ valuation q 1643 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1644 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1644)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 7 3 (meaning1567 q) (meaning1622 q) (meaning1644 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1622 = false ∨ valuation q 1644 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1644 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1644)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 8 2 (meaning1568 q) (meaning1621 q) (meaning1644 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1621 = false ∨ valuation q 1644 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1645 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1645)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 8 3 (meaning1568 q) (meaning1622 q) (meaning1645 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1622 = false ∨ valuation q 1645 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1646 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1646)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 8 4 (meaning1568 q) (meaning1623 q) (meaning1646 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1623 = false ∨ valuation q 1646 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1672 = true := by
  have hs : count1654 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1672)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1654 q) 7 12 (meaning1504 q) (meaning1646 q) (meaning1672 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1646 = false ∨ valuation q 1672 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1672 = true := by
  have hs : count1654 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1672)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1654 q) 8 11 (meaning1505 q) (meaning1645 q) (meaning1672 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1645 = false ∨ valuation q 1672 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1672 = true := by
  have hs : count1654 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1672)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1654 q) 9 10 (meaning1506 q) (meaning1644 q) (meaning1672 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1644 = false ∨ valuation q 1672 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1672 = true := by
  have hs : count1654 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1672)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1654 q) 10 9 (meaning1507 q) (meaning1643 q) (meaning1672 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1643 = false ∨ valuation q 1672 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1672 = true := by
  have hs : count1654 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) + (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (l₂ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1672)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28, -29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87, -88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1654 q) 11 8 (meaning1508 q) (meaning1642 q) (meaning1672 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1642 = false ∨ valuation q 1672 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E088.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112088
