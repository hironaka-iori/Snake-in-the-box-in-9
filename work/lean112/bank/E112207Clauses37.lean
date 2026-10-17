import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1562 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-75]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1565)) (countLit q [-75]) (countLit q [-79, -80]) (count1564 q) 1 1 (meaningNeg75 q) (meaning1562 q) (meaning1565 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1562 = false ∨ valuation q 1565 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1567 = true := by
  have hs : count1567 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1567)) (countLit q [-81]) (countLit q [-82]) (count1567 q) 1 (meaningNeg82 q) (meaning1567 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1567 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1567 = true := by
  have hs : count1567 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1567)) (countLit q [-81]) (countLit q [-82]) (count1567 q) 1 (meaningNeg81 q) (meaning1567 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1567 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1568 = true := by
  have hs : count1567 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1568)) (countLit q [-81]) (countLit q [-82]) (count1567 q) 1 1 (meaningNeg81 q) (meaningNeg82 q) (meaning1568 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 1568 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1569 = true := by
  have hs : count1569 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1569)) (countLit q [-86]) (countLit q [-89]) (count1569 q) 1 (meaningNeg89 q) (meaning1569 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1569 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1569 = true := by
  have hs : count1569 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1569)) (countLit q [-86]) (countLit q [-89]) (count1569 q) 1 (meaningNeg86 q) (meaning1569 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1569 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 89 = true ∨ valuationOf q 1570 = true := by
  have hs : count1569 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-89)) (literal (valuationOf q) (1570)) (countLit q [-86]) (countLit q [-89]) (count1569 q) 1 1 (meaningNeg86 q) (meaningNeg89 q) (meaning1570 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 89)) = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 89 = true ∨ valuation q 1570 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-81, -82]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-86, -89])
  have hm := merge_right (literal (valuationOf q) (1569)) (literal (valuationOf q) (1571)) (countLit q [-81, -82]) (countLit q [-86, -89]) (count1571 q) 1 (meaning1569 q) (meaning1571 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1571 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-81, -82]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-86, -89])
  have hm := merge_right (literal (valuationOf q) (1570)) (literal (valuationOf q) (1572)) (countLit q [-81, -82]) (countLit q [-86, -89]) (count1571 q) 2 (meaning1570 q) (meaning1572 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1572 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-81, -82]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-86, -89])
  have hm := merge_left (literal (valuationOf q) (1567)) (literal (valuationOf q) (1571)) (countLit q [-81, -82]) (countLit q [-86, -89]) (count1571 q) 1 (meaning1567 q) (meaning1571 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1571 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-81, -82]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1572)) (countLit q [-81, -82]) (countLit q [-86, -89]) (count1571 q) 1 1 (meaning1567 q) (meaning1569 q) (meaning1572 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1569 = false ∨ valuation q 1572 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1573 = true := by
  have hs : count1571 q = (countLit q [-81, -82]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1573)) (countLit q [-81, -82]) (countLit q [-86, -89]) (count1571 q) 1 2 (meaning1567 q) (meaning1570 q) (meaning1573 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1570 = false ∨ valuation q 1573 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-81, -82]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-86, -89])
  have hm := merge_left (literal (valuationOf q) (1568)) (literal (valuationOf q) (1572)) (countLit q [-81, -82]) (countLit q [-86, -89]) (count1571 q) 2 (meaning1568 q) (meaning1572 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1572 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1573 = true := by
  have hs : count1571 q = (countLit q [-81, -82]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1573)) (countLit q [-81, -82]) (countLit q [-86, -89]) (count1571 q) 2 1 (meaning1568 q) (meaning1569 q) (meaning1573 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1569 = false ∨ valuation q 1573 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1571)) (literal (valuationOf q) (1575)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1575 q) 1 (meaning1571 q) (meaning1575 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1575 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1572)) (literal (valuationOf q) (1576)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1575 q) 2 (meaning1572 q) (meaning1576 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1576 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1577 = true := by
  have hs : count1575 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1573)) (literal (valuationOf q) (1577)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1575 q) 3 (meaning1573 q) (meaning1577 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1577 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1564)) (literal (valuationOf q) (1575)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1575 q) 1 (meaning1564 q) (meaning1575 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1575 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1576)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1575 q) 1 1 (meaning1564 q) (meaning1571 q) (meaning1576 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1571 = false ∨ valuation q 1576 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1577 = true := by
  have hs : count1575 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1577)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1575 q) 1 2 (meaning1564 q) (meaning1572 q) (meaning1577 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1572 = false ∨ valuation q 1577 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1565)) (literal (valuationOf q) (1576)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1575 q) 2 (meaning1565 q) (meaning1576 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1576 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1577 = true := by
  have hs : count1575 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1577)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1575 q) 2 1 (meaning1565 q) (meaning1571 q) (meaning1577 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1571 = false ∨ valuation q 1577 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1576)) (literal (valuationOf q) (1583)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 2 (meaning1576 q) (meaning1583 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1583 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1577)) (literal (valuationOf q) (1584)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 3 (meaning1577 q) (meaning1584 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1584 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1583)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 1 1 (meaning1555 q) (meaning1575 q) (meaning1583 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1575 = false ∨ valuation q 1583 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1584)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 1 2 (meaning1555 q) (meaning1576 q) (meaning1584 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1576 = false ∨ valuation q 1584 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1585 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1585)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 1 3 (meaning1555 q) (meaning1577 q) (meaning1585 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1577 = false ∨ valuation q 1585 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1556)) (literal (valuationOf q) (1583)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 2 (meaning1556 q) (meaning1583 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1583 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1584)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 2 1 (meaning1556 q) (meaning1575 q) (meaning1584 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1575 = false ∨ valuation q 1584 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1585 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1585)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 2 2 (meaning1556 q) (meaning1576 q) (meaning1585 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1576 = false ∨ valuation q 1585 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1586 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1586)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 2 3 (meaning1556 q) (meaning1577 q) (meaning1586 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1577 = false ∨ valuation q 1586 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1585 = true := by
  have hs : count1582 q = (countLit q [-62, -63, -66, -69, -71, -72, -74]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -66, -69, -71, -72, -74]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1585)) (countLit q [-62, -63, -66, -69, -71, -72, -74]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1582 q) 3 1 (meaning1557 q) (meaning1575 q) (meaning1585 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1575 = false ∨ valuation q 1585 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E207.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112207
