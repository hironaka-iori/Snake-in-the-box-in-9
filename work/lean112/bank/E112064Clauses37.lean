import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1567 = true := by
  have hs : count1567 q = (countLit q [-81, -82]) + (countLit q [-83, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-83, -86])
  have hm := merge_right (literal (valuationOf q) (1565)) (literal (valuationOf q) (1567)) (countLit q [-81, -82]) (countLit q [-83, -86]) (count1567 q) 1 (meaning1565 q) (meaning1567 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1567 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1568 = true := by
  have hs : count1567 q = (countLit q [-81, -82]) + (countLit q [-83, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-83, -86])
  have hm := merge_right (literal (valuationOf q) (1566)) (literal (valuationOf q) (1568)) (countLit q [-81, -82]) (countLit q [-83, -86]) (count1567 q) 2 (meaning1566 q) (meaning1568 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1568 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1567 = true := by
  have hs : count1567 q = (countLit q [-81, -82]) + (countLit q [-83, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-83, -86])
  have hm := merge_left (literal (valuationOf q) (1563)) (literal (valuationOf q) (1567)) (countLit q [-81, -82]) (countLit q [-83, -86]) (count1567 q) 1 (meaning1563 q) (meaning1567 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1567 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1568 = true := by
  have hs : count1567 q = (countLit q [-81, -82]) + (countLit q [-83, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-83, -86])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1568)) (countLit q [-81, -82]) (countLit q [-83, -86]) (count1567 q) 1 1 (meaning1563 q) (meaning1565 q) (meaning1568 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1565 = false ∨ valuation q 1568 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1569 = true := by
  have hs : count1567 q = (countLit q [-81, -82]) + (countLit q [-83, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-83, -86])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1569)) (countLit q [-81, -82]) (countLit q [-83, -86]) (count1567 q) 1 2 (meaning1563 q) (meaning1566 q) (meaning1569 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1566 = false ∨ valuation q 1569 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1568 = true := by
  have hs : count1567 q = (countLit q [-81, -82]) + (countLit q [-83, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-83, -86])
  have hm := merge_left (literal (valuationOf q) (1564)) (literal (valuationOf q) (1568)) (countLit q [-81, -82]) (countLit q [-83, -86]) (count1567 q) 2 (meaning1564 q) (meaning1568 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1568 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1569 = true := by
  have hs : count1567 q = (countLit q [-81, -82]) + (countLit q [-83, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-83, -86])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1569)) (countLit q [-81, -82]) (countLit q [-83, -86]) (count1567 q) 2 1 (meaning1564 q) (meaning1565 q) (meaning1569 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1565 = false ∨ valuation q 1569 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1570 = true := by
  have hs : count1567 q = (countLit q [-81, -82]) + (countLit q [-83, -86]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-83, -86])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1570)) (countLit q [-81, -82]) (countLit q [-83, -86]) (count1567 q) 2 2 (meaning1564 q) (meaning1566 q) (meaning1570 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1566 = false ∨ valuation q 1570 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_right (literal (valuationOf q) (1567)) (literal (valuationOf q) (1571)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 1 (meaning1567 q) (meaning1571 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1571 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_right (literal (valuationOf q) (1568)) (literal (valuationOf q) (1572)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 2 (meaning1568 q) (meaning1572 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1572 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1573 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_right (literal (valuationOf q) (1569)) (literal (valuationOf q) (1573)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 3 (meaning1569 q) (meaning1573 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1573 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1574 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_right (literal (valuationOf q) (1570)) (literal (valuationOf q) (1574)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 4 (meaning1570 q) (meaning1574 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1574 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_left (literal (valuationOf q) (1559)) (literal (valuationOf q) (1571)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 1 (meaning1559 q) (meaning1571 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1571 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1572)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 1 1 (meaning1559 q) (meaning1567 q) (meaning1572 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1567 = false ∨ valuation q 1572 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1573 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1573)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 1 2 (meaning1559 q) (meaning1568 q) (meaning1573 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1568 = false ∨ valuation q 1573 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1574 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1574)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 1 3 (meaning1559 q) (meaning1569 q) (meaning1574 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1569 = false ∨ valuation q 1574 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1575 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1575)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 1 4 (meaning1559 q) (meaning1570 q) (meaning1575 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1570 = false ∨ valuation q 1575 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_left (literal (valuationOf q) (1560)) (literal (valuationOf q) (1572)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 2 (meaning1560 q) (meaning1572 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1572 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1573 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1573)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 2 1 (meaning1560 q) (meaning1567 q) (meaning1573 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1567 = false ∨ valuation q 1573 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1574 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1574)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 2 2 (meaning1560 q) (meaning1568 q) (meaning1574 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1568 = false ∨ valuation q 1574 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1575 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1575)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 2 3 (meaning1560 q) (meaning1569 q) (meaning1575 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1569 = false ∨ valuation q 1575 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1576 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1576)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 2 4 (meaning1560 q) (meaning1570 q) (meaning1576 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1570 = false ∨ valuation q 1576 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1574 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1574)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 3 1 (meaning1561 q) (meaning1567 q) (meaning1574 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1567 = false ∨ valuation q 1574 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1575 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1575)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 3 2 (meaning1561 q) (meaning1568 q) (meaning1575 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1568 = false ∨ valuation q 1575 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1576 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1576)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 3 3 (meaning1561 q) (meaning1569 q) (meaning1576 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1569 = false ∨ valuation q 1576 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1577 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1577)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 3 4 (meaning1561 q) (meaning1570 q) (meaning1577 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1570 = false ∨ valuation q 1577 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1575 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1575)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 4 1 (meaning1562 q) (meaning1567 q) (meaning1575 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1567 = false ∨ valuation q 1575 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1576 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1568)) (literal (valuationOf q) (1576)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 4 2 (meaning1562 q) (meaning1568 q) (meaning1576 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1568 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1568 = false ∨ valuation q 1576 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1577 = true := by
  have hs : count1571 q = (countLit q [-72, -74, -76, -78]) + (countLit q [-81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -74, -76, -78]) (l₂ := [-81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1577)) (countLit q [-72, -74, -76, -78]) (countLit q [-81, -82, -83, -86]) (count1571 q) 4 3 (meaning1562 q) (meaning1569 q) (meaning1577 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1569 = false ∨ valuation q 1577 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_right (literal (valuationOf q) (1572)) (literal (valuationOf q) (1580)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 2 (meaning1572 q) (meaning1580 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1580 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1581 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_right (literal (valuationOf q) (1573)) (literal (valuationOf q) (1581)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 3 (meaning1573 q) (meaning1581 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1581 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1582 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_right (literal (valuationOf q) (1574)) (literal (valuationOf q) (1582)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 4 (meaning1574 q) (meaning1582 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1582 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E064.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112064
