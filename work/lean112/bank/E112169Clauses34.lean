import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-86, -88, -91, -93, -94, -97, -100]) + (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -91, -93, -94, -97, -100]) (l₂ := [-102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1629)) (countLit q [-86, -88, -91, -93, -94, -97, -100]) (countLit q [-102, -103, -105, -106, -110, -112, -113, -114]) (count1624 q) 4 2 (meaning1596 q) (meaning1617 q) (meaning1629 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1617 = false ∨ valuation q 1629 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1643 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1643)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 1 4 (meaning1566 q) (meaning1627 q) (meaning1643 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1627 = false ∨ valuation q 1643 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1641 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1641)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 2 1 (meaning1567 q) (meaning1624 q) (meaning1641 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1624 = false ∨ valuation q 1641 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1642 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1642)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 2 2 (meaning1567 q) (meaning1625 q) (meaning1642 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1625 = false ∨ valuation q 1642 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1643 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1643)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 2 3 (meaning1567 q) (meaning1626 q) (meaning1643 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1626 = false ∨ valuation q 1643 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1644 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1644)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 2 4 (meaning1567 q) (meaning1627 q) (meaning1644 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1627 = false ∨ valuation q 1644 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1645 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1645)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 2 5 (meaning1567 q) (meaning1628 q) (meaning1645 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1628 = false ∨ valuation q 1645 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1646 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1646)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 2 6 (meaning1567 q) (meaning1629 q) (meaning1646 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1629 = false ∨ valuation q 1646 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1643 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1643)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 3 2 (meaning1568 q) (meaning1625 q) (meaning1643 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1625 = false ∨ valuation q 1643 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1644 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1644)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 3 3 (meaning1568 q) (meaning1626 q) (meaning1644 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1626 = false ∨ valuation q 1644 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1645 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1645)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 3 4 (meaning1568 q) (meaning1627 q) (meaning1645 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1627 = false ∨ valuation q 1645 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1646 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1646)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 3 5 (meaning1568 q) (meaning1628 q) (meaning1646 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1628 = false ∨ valuation q 1646 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1644 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1644)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 4 2 (meaning1569 q) (meaning1625 q) (meaning1644 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1625 = false ∨ valuation q 1644 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1645 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1645)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 4 3 (meaning1569 q) (meaning1626 q) (meaning1645 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1626 = false ∨ valuation q 1645 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1646 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1646)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 4 4 (meaning1569 q) (meaning1627 q) (meaning1646 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1627 = false ∨ valuation q 1646 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1647 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1647)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 4 5 (meaning1569 q) (meaning1628 q) (meaning1647 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1628 = false ∨ valuation q 1647 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1645 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1645)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 5 2 (meaning1570 q) (meaning1625 q) (meaning1645 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1625 = false ∨ valuation q 1645 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1646 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1646)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 5 3 (meaning1570 q) (meaning1626 q) (meaning1646 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1626 = false ∨ valuation q 1646 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1647 = true := by
  have hs : count1639 q = (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) + (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (l₂ := [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1647)) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85]) (countLit q [-86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1639 q) 5 4 (meaning1570 q) (meaning1627 q) (meaning1647 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1627 = false ∨ valuation q 1647 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) + (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (l₂ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1672)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1656 q) 8 9 (meaning1516 q) (meaning1647 q) (meaning1672 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1647 = false ∨ valuation q 1672 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) + (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (l₂ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1672)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1656 q) 9 8 (meaning1517 q) (meaning1646 q) (meaning1672 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1646 = false ∨ valuation q 1672 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) + (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (l₂ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1672)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1656 q) 10 7 (meaning1518 q) (meaning1645 q) (meaning1672 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1645 = false ∨ valuation q 1672 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) + (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (l₂ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1672)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1656 q) 11 6 (meaning1519 q) (meaning1644 q) (meaning1672 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1644 = false ∨ valuation q 1672 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) + (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (l₂ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1672)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1656 q) 12 5 (meaning1520 q) (meaning1643 q) (meaning1672 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1643 = false ∨ valuation q 1672 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) + (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (l₂ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1672)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1656 q) 13 4 (meaning1521 q) (meaning1642 q) (meaning1672 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1642 = false ∨ valuation q 1672 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1672 = true := by
  have hs : count1656 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) + (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (l₂ := [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1672)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27, -30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (countLit q [-57, -59, -63, -65, -67, -69, -70, -72, -75, -77, -78, -80, -83, -85, -86, -88, -91, -93, -94, -97, -100, -102, -103, -105, -106, -110, -112, -113, -114]) (count1656 q) 14 3 (meaning1522 q) (meaning1641 q) (meaning1672 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1641 = false ∨ valuation q 1672 = true := counterClause1114 (baseVal q)

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false := by
  rw [value1672]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1656 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 31 = false ∨ valuation q 37 = false := by
  rw [value7, value9, value31, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (96 : Vertex) (104 : Vertex) (224 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 26 = false := by
  rw [value11, value17, value21, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (176 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 17 = false ∨ valuation q 31 = false ∨ valuation q 37 = false := by
  rw [value11, value17, value31, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (224 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 24 = false := by
  rw [value12, value14, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (163 : Vertex) (177 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value13, value14, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (162 : Vertex) (163 : Vertex) (178 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E169.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112169
