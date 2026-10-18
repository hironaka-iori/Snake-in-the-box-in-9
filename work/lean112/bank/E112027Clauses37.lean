import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-75]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76, -77])
  have hm := merge_right (literal (valuationOf q) (1583)) (literal (valuationOf q) (1585)) (countLit q [-75]) (countLit q [-76, -77]) (count1584 q) 2 (meaning1583 q) (meaning1585 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1585 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1584 = true := by
  have hs : count1584 q = (countLit q [-75]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76, -77])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1584)) (countLit q [-75]) (countLit q [-76, -77]) (count1584 q) 1 (meaningNeg75 q) (meaning1584 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1584 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1582 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-75]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76, -77])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1585)) (countLit q [-75]) (countLit q [-76, -77]) (count1584 q) 1 1 (meaningNeg75 q) (meaning1582 q) (meaning1585 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1582 = false ∨ valuation q 1585 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1583 = false ∨ valuationOf q 1586 = true := by
  have hs : count1584 q = (countLit q [-75]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76, -77])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1586)) (countLit q [-75]) (countLit q [-76, -77]) (count1584 q) 1 2 (meaningNeg75 q) (meaning1583 q) (meaning1586 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1583 = false ∨ valuation q 1586 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1587)) (countLit q [-81]) (countLit q [-82]) (count1587 q) 1 (meaningNeg82 q) (meaning1587 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1587 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1587)) (countLit q [-81]) (countLit q [-82]) (count1587 q) 1 (meaningNeg81 q) (meaning1587 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1587 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1588)) (countLit q [-81]) (countLit q [-82]) (count1587 q) 1 1 (meaningNeg81 q) (meaningNeg82 q) (meaning1588 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 1588 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-85]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1589)) (countLit q [-85]) (countLit q [-89]) (count1589 q) 1 (meaningNeg89 q) (meaning1589 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1589 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-85]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1589)) (countLit q [-85]) (countLit q [-89]) (count1589 q) 1 (meaningNeg85 q) (meaning1589 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1589 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 89 = true ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-85]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-89])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-89)) (literal (valuationOf q) (1590)) (countLit q [-85]) (countLit q [-89]) (count1589 q) 1 1 (meaningNeg85 q) (meaningNeg89 q) (meaning1590 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 89)) = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 89 = true ∨ valuation q 1590 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-81, -82]) + (countLit q [-85, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -89])
  have hm := merge_right (literal (valuationOf q) (1589)) (literal (valuationOf q) (1591)) (countLit q [-81, -82]) (countLit q [-85, -89]) (count1591 q) 1 (meaning1589 q) (meaning1591 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1591 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-81, -82]) + (countLit q [-85, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -89])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1592)) (countLit q [-81, -82]) (countLit q [-85, -89]) (count1591 q) 2 (meaning1590 q) (meaning1592 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1592 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-81, -82]) + (countLit q [-85, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -89])
  have hm := merge_left (literal (valuationOf q) (1587)) (literal (valuationOf q) (1591)) (countLit q [-81, -82]) (countLit q [-85, -89]) (count1591 q) 1 (meaning1587 q) (meaning1591 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1591 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-81, -82]) + (countLit q [-85, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -89])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1592)) (countLit q [-81, -82]) (countLit q [-85, -89]) (count1591 q) 1 1 (meaning1587 q) (meaning1589 q) (meaning1592 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1589 = false ∨ valuation q 1592 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-81, -82]) + (countLit q [-85, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -89])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1593)) (countLit q [-81, -82]) (countLit q [-85, -89]) (count1591 q) 1 2 (meaning1587 q) (meaning1590 q) (meaning1593 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1590 = false ∨ valuation q 1593 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-81, -82]) + (countLit q [-85, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -89])
  have hm := merge_left (literal (valuationOf q) (1588)) (literal (valuationOf q) (1592)) (countLit q [-81, -82]) (countLit q [-85, -89]) (count1591 q) 2 (meaning1588 q) (meaning1592 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1592 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-81, -82]) + (countLit q [-85, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -89])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1593)) (countLit q [-81, -82]) (countLit q [-85, -89]) (count1591 q) 2 1 (meaning1588 q) (meaning1589 q) (meaning1593 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1589 = false ∨ valuation q 1593 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1594 = true := by
  have hs : count1591 q = (countLit q [-81, -82]) + (countLit q [-85, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-85, -89])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1594)) (countLit q [-81, -82]) (countLit q [-85, -89]) (count1591 q) 2 2 (meaning1588 q) (meaning1590 q) (meaning1594 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1590 = false ∨ valuation q 1594 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1596 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_right (literal (valuationOf q) (1592)) (literal (valuationOf q) (1596)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 2 (meaning1592 q) (meaning1596 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1596 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1597 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_right (literal (valuationOf q) (1593)) (literal (valuationOf q) (1597)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 3 (meaning1593 q) (meaning1597 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1597 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_right (literal (valuationOf q) (1594)) (literal (valuationOf q) (1598)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 4 (meaning1594 q) (meaning1598 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1598 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1595 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_left (literal (valuationOf q) (1584)) (literal (valuationOf q) (1595)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 1 (meaning1584 q) (meaning1595 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1595 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1596 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1596)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 1 1 (meaning1584 q) (meaning1591 q) (meaning1596 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1591 = false ∨ valuation q 1596 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1597 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1597)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 1 2 (meaning1584 q) (meaning1592 q) (meaning1597 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1592 = false ∨ valuation q 1597 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1598)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 1 3 (meaning1584 q) (meaning1593 q) (meaning1598 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1593 = false ∨ valuation q 1598 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1599)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 1 4 (meaning1584 q) (meaning1594 q) (meaning1599 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1594 = false ∨ valuation q 1599 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1596 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_left (literal (valuationOf q) (1585)) (literal (valuationOf q) (1596)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 2 (meaning1585 q) (meaning1596 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1596 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1597 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1597)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 2 1 (meaning1585 q) (meaning1591 q) (meaning1597 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1591 = false ∨ valuation q 1597 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1598 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1598)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 2 2 (meaning1585 q) (meaning1592 q) (meaning1598 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1592 = false ∨ valuation q 1598 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1599 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1599)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 2 3 (meaning1585 q) (meaning1593 q) (meaning1599 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1593 = false ∨ valuation q 1599 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1600 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1600)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 2 4 (meaning1585 q) (meaning1594 q) (meaning1600 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1594 = false ∨ valuation q 1600 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1597 = true := by
  have hs : count1595 q = (countLit q [-75, -76, -77]) + (countLit q [-81, -82, -85, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -77]) (l₂ := [-81, -82, -85, -89])
  have hm := merge_left (literal (valuationOf q) (1586)) (literal (valuationOf q) (1597)) (countLit q [-75, -76, -77]) (countLit q [-81, -82, -85, -89]) (count1595 q) 3 (meaning1586 q) (meaning1597 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1597 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E027.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112027
