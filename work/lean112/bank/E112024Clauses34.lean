import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 85 = true ∨ valuationOf q 1622 = true := by
  have hs : count1621 q = (countLit q [-81]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (1622)) (countLit q [-81]) (countLit q [-85]) (count1621 q) 1 1 (meaningNeg81 q) (meaningNeg85 q) (meaning1622 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 1622 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1623)) (countLit q [-86]) (countLit q [-89]) (count1623 q) 1 (meaningNeg89 q) (meaning1623 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1623 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1623)) (countLit q [-86]) (countLit q [-89]) (count1623 q) 1 (meaningNeg86 q) (meaning1623 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1623 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 89 = true ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-89)) (literal (valuationOf q) (1624)) (countLit q [-86]) (countLit q [-89]) (count1623 q) 1 1 (meaningNeg86 q) (meaningNeg89 q) (meaning1624 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 89)) = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 89 = true ∨ valuation q 1624 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-81, -85]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -85]) (l₂ := [-86, -89])
  have hm := merge_right (literal (valuationOf q) (1623)) (literal (valuationOf q) (1625)) (countLit q [-81, -85]) (countLit q [-86, -89]) (count1625 q) 1 (meaning1623 q) (meaning1625 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1625 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-81, -85]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -85]) (l₂ := [-86, -89])
  have hm := merge_right (literal (valuationOf q) (1624)) (literal (valuationOf q) (1626)) (countLit q [-81, -85]) (countLit q [-86, -89]) (count1625 q) 2 (meaning1624 q) (meaning1626 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1626 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-81, -85]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -85]) (l₂ := [-86, -89])
  have hm := merge_left (literal (valuationOf q) (1621)) (literal (valuationOf q) (1625)) (countLit q [-81, -85]) (countLit q [-86, -89]) (count1625 q) 1 (meaning1621 q) (meaning1625 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1625 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-81, -85]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -85]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1626)) (countLit q [-81, -85]) (countLit q [-86, -89]) (count1625 q) 1 1 (meaning1621 q) (meaning1623 q) (meaning1626 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1623 = false ∨ valuation q 1626 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1627 = true := by
  have hs : count1625 q = (countLit q [-81, -85]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -85]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1627)) (countLit q [-81, -85]) (countLit q [-86, -89]) (count1625 q) 1 2 (meaning1621 q) (meaning1624 q) (meaning1627 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1624 = false ∨ valuation q 1627 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-81, -85]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -85]) (l₂ := [-86, -89])
  have hm := merge_left (literal (valuationOf q) (1622)) (literal (valuationOf q) (1626)) (countLit q [-81, -85]) (countLit q [-86, -89]) (count1625 q) 2 (meaning1622 q) (meaning1626 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1626 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1627 = true := by
  have hs : count1625 q = (countLit q [-81, -85]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -85]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1627)) (countLit q [-81, -85]) (countLit q [-86, -89]) (count1625 q) 2 1 (meaning1622 q) (meaning1623 q) (meaning1627 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1623 = false ∨ valuation q 1627 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1628 = true := by
  have hs : count1625 q = (countLit q [-81, -85]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -85]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1628)) (countLit q [-81, -85]) (countLit q [-86, -89]) (count1625 q) 2 2 (meaning1622 q) (meaning1624 q) (meaning1628 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1624 = false ∨ valuation q 1628 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1629 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1617)) (literal (valuationOf q) (1629)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 1 (meaning1617 q) (meaning1629 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1629 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1630 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1630)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 1 1 (meaning1617 q) (meaning1625 q) (meaning1630 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1625 = false ∨ valuation q 1630 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1631 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1631)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 1 2 (meaning1617 q) (meaning1626 q) (meaning1631 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1626 = false ∨ valuation q 1631 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1632 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1632)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 1 3 (meaning1617 q) (meaning1627 q) (meaning1632 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1627 = false ∨ valuation q 1632 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1633 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1633)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 1 4 (meaning1617 q) (meaning1628 q) (meaning1633 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1628 = false ∨ valuation q 1633 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1630 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1618)) (literal (valuationOf q) (1630)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 2 (meaning1618 q) (meaning1630 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1630 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1631 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1631)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 2 1 (meaning1618 q) (meaning1625 q) (meaning1631 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1625 = false ∨ valuation q 1631 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1632 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1632)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 2 2 (meaning1618 q) (meaning1626 q) (meaning1632 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1626 = false ∨ valuation q 1632 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1633 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1633)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 2 3 (meaning1618 q) (meaning1627 q) (meaning1633 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1627 = false ∨ valuation q 1633 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1634 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1634)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 2 4 (meaning1618 q) (meaning1628 q) (meaning1634 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1628 = false ∨ valuation q 1634 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1631 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1619)) (literal (valuationOf q) (1631)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 3 (meaning1619 q) (meaning1631 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1631 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1632 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1632)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 3 1 (meaning1619 q) (meaning1625 q) (meaning1632 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1625 = false ∨ valuation q 1632 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1633 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1633)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 3 2 (meaning1619 q) (meaning1626 q) (meaning1633 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1626 = false ∨ valuation q 1633 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1634 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1634)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 3 3 (meaning1619 q) (meaning1627 q) (meaning1634 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1627 = false ∨ valuation q 1634 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1633 = true := by
  have hs : count1629 q = (countLit q [-74, -76, -77, -79]) + (countLit q [-81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77, -79]) (l₂ := [-81, -85, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1633)) (countLit q [-74, -76, -77, -79]) (countLit q [-81, -85, -86, -89]) (count1629 q) 4 1 (meaning1620 q) (meaning1625 q) (meaning1633 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1625 = false ∨ valuation q 1633 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1629)) (literal (valuationOf q) (1637)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 1 (meaning1629 q) (meaning1637 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1637 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1638 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1630)) (literal (valuationOf q) (1638)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 2 (meaning1630 q) (meaning1638 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1638 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1639 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1631)) (literal (valuationOf q) (1639)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 3 (meaning1631 q) (meaning1639 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1639 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1640 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1640)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 4 (meaning1632 q) (meaning1640 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1640 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1641 = true := by
  have hs : count1637 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) + (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72]) (l₂ := [-74, -76, -77, -79, -81, -85, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1641)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72]) (countLit q [-74, -76, -77, -79, -81, -85, -86, -89]) (count1637 q) 5 (meaning1633 q) (meaning1641 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1641 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E024.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112024
