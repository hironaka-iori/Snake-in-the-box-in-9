import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-111, -112]) + (countLit q [-113, -116]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -116])
  have hm := merge_left (literal (valuationOf q) (1605)) (literal (valuationOf q) (1609)) (countLit q [-111, -112]) (countLit q [-113, -116]) (count1608 q) 2 (meaning1605 q) (meaning1609 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1609 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-103, -105, -107, -108]) + (countLit q [-111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -105, -107, -108]) (l₂ := [-111, -112, -113, -116])
  have hm := merge_right (literal (valuationOf q) (1608)) (literal (valuationOf q) (1612)) (countLit q [-103, -105, -107, -108]) (countLit q [-111, -112, -113, -116]) (count1612 q) 1 (meaning1608 q) (meaning1612 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1612 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-103, -105, -107, -108]) + (countLit q [-111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -105, -107, -108]) (l₂ := [-111, -112, -113, -116])
  have hm := merge_right (literal (valuationOf q) (1609)) (literal (valuationOf q) (1613)) (countLit q [-103, -105, -107, -108]) (countLit q [-111, -112, -113, -116]) (count1612 q) 2 (meaning1609 q) (meaning1613 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1613 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-103, -105, -107, -108]) + (countLit q [-111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -105, -107, -108]) (l₂ := [-111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1613)) (countLit q [-103, -105, -107, -108]) (countLit q [-111, -112, -113, -116]) (count1612 q) 1 1 (meaning1600 q) (meaning1608 q) (meaning1613 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1608 = false ∨ valuation q 1613 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-103, -105, -107, -108]) + (countLit q [-111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -105, -107, -108]) (l₂ := [-111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1614)) (countLit q [-103, -105, -107, -108]) (countLit q [-111, -112, -113, -116]) (count1612 q) 1 2 (meaning1600 q) (meaning1609 q) (meaning1614 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1609 = false ∨ valuation q 1614 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-103, -105, -107, -108]) + (countLit q [-111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -105, -107, -108]) (l₂ := [-111, -112, -113, -116])
  have hm := merge_left (literal (valuationOf q) (1601)) (literal (valuationOf q) (1613)) (countLit q [-103, -105, -107, -108]) (countLit q [-111, -112, -113, -116]) (count1612 q) 2 (meaning1601 q) (meaning1613 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1613 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-103, -105, -107, -108]) + (countLit q [-111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -105, -107, -108]) (l₂ := [-111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1614)) (countLit q [-103, -105, -107, -108]) (countLit q [-111, -112, -113, -116]) (count1612 q) 2 1 (meaning1601 q) (meaning1608 q) (meaning1614 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1608 = false ∨ valuation q 1614 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1615 = true := by
  have hs : count1612 q = (countLit q [-103, -105, -107, -108]) + (countLit q [-111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-103, -105, -107, -108]) (l₂ := [-111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1615)) (countLit q [-103, -105, -107, -108]) (countLit q [-111, -112, -113, -116]) (count1612 q) 2 2 (meaning1601 q) (meaning1609 q) (meaning1615 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1609 = false ∨ valuation q 1615 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1620 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_right (literal (valuationOf q) (1612)) (literal (valuationOf q) (1620)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 1 (meaning1612 q) (meaning1620 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1620 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1621 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_right (literal (valuationOf q) (1613)) (literal (valuationOf q) (1621)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 2 (meaning1613 q) (meaning1621 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1621 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1622 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_right (literal (valuationOf q) (1614)) (literal (valuationOf q) (1622)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 3 (meaning1614 q) (meaning1622 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1622 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1623 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_right (literal (valuationOf q) (1615)) (literal (valuationOf q) (1623)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 4 (meaning1615 q) (meaning1623 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1623 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1621 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1621)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 1 1 (meaning1589 q) (meaning1612 q) (meaning1621 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1612 = false ∨ valuation q 1621 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1622 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1622)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 1 2 (meaning1589 q) (meaning1613 q) (meaning1622 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1613 = false ∨ valuation q 1622 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1623 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1623)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 1 3 (meaning1589 q) (meaning1614 q) (meaning1623 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1614 = false ∨ valuation q 1623 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1624 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1624)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 1 4 (meaning1589 q) (meaning1615 q) (meaning1624 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1615 = false ∨ valuation q 1624 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1622 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1590)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1622)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 2 1 (meaning1590 q) (meaning1612 q) (meaning1622 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1612 = false ∨ valuation q 1622 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1623 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1590)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1623)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 2 2 (meaning1590 q) (meaning1613 q) (meaning1623 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1613 = false ∨ valuation q 1623 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1624 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1590)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1624)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 2 3 (meaning1590 q) (meaning1614 q) (meaning1624 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1614 = false ∨ valuation q 1624 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1623 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1623)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 3 1 (meaning1591 q) (meaning1612 q) (meaning1623 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1612 = false ∨ valuation q 1623 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1624 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1624)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 3 2 (meaning1591 q) (meaning1613 q) (meaning1624 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1613 = false ∨ valuation q 1624 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1625 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1625)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 3 3 (meaning1591 q) (meaning1614 q) (meaning1625 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1614 = false ∨ valuation q 1625 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1623 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_left (literal (valuationOf q) (1592)) (literal (valuationOf q) (1623)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 4 (meaning1592 q) (meaning1623 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1623 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1624 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1624)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 4 1 (meaning1592 q) (meaning1612 q) (meaning1624 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1612 = false ∨ valuation q 1624 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1625 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1625)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 4 2 (meaning1592 q) (meaning1613 q) (meaning1625 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1613 = false ∨ valuation q 1625 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1626 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1626)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 4 3 (meaning1592 q) (meaning1614 q) (meaning1626 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1614 = false ∨ valuation q 1626 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1625 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1625)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 5 1 (meaning1593 q) (meaning1612 q) (meaning1625 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1612 = false ∨ valuation q 1625 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1626 = true := by
  have hs : count1620 q = (countLit q [-88, -90, -92, -94, -95, -97, -100]) + (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92, -94, -95, -97, -100]) (l₂ := [-103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1626)) (countLit q [-88, -90, -92, -94, -95, -97, -100]) (countLit q [-103, -105, -107, -108, -111, -112, -113, -116]) (count1620 q) 5 2 (meaning1593 q) (meaning1613 q) (meaning1626 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1613 = false ∨ valuation q 1626 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1640 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1640)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 2 4 (meaning1562 q) (meaning1623 q) (meaning1640 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1623 = false ∨ valuation q 1640 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1638 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1638)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 3 1 (meaning1563 q) (meaning1620 q) (meaning1638 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1620 = false ∨ valuation q 1638 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1640 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1640)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 3 3 (meaning1563 q) (meaning1622 q) (meaning1640 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1622 = false ∨ valuation q 1640 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1641 = true := by
  have hs : count1635 q = (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) + (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (l₂ := [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1641)) (countLit q [-59, -61, -63, -64, -66, -69, -71, -73, -75, -77, -78, -80, -82, -85, -87]) (countLit q [-88, -90, -92, -94, -95, -97, -100, -103, -105, -107, -108, -111, -112, -113, -116]) (count1635 q) 3 4 (meaning1563 q) (meaning1623 q) (meaning1641 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1623 = false ∨ valuation q 1641 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E088.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112088
