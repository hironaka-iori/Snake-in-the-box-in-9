import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1583 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_right (literal (valuationOf q) (1575)) (literal (valuationOf q) (1583)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 5 (meaning1575 q) (meaning1583 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1583 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1584 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_right (literal (valuationOf q) (1576)) (literal (valuationOf q) (1584)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 6 (meaning1576 q) (meaning1584 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1584 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1571)) (literal (valuationOf q) (1580)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 1 1 (meaning1548 q) (meaning1571 q) (meaning1580 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1571 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1571 = false ∨ valuation q 1580 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1581 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1581)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 1 2 (meaning1548 q) (meaning1572 q) (meaning1581 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1572 = false ∨ valuation q 1581 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1582 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1582)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 1 3 (meaning1548 q) (meaning1573 q) (meaning1582 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1573 = false ∨ valuation q 1582 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1583 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1583)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 1 4 (meaning1548 q) (meaning1574 q) (meaning1583 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1574 = false ∨ valuation q 1583 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1584 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1584)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 1 5 (meaning1548 q) (meaning1575 q) (meaning1584 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1575 = false ∨ valuation q 1584 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1585 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1585)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 1 6 (meaning1548 q) (meaning1576 q) (meaning1585 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1576 = false ∨ valuation q 1585 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1586 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1586)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 1 7 (meaning1548 q) (meaning1577 q) (meaning1586 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1577 = false ∨ valuation q 1586 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1582 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1582)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 2 2 (meaning1549 q) (meaning1572 q) (meaning1582 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1572 = false ∨ valuation q 1582 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1583 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1583)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 2 3 (meaning1549 q) (meaning1573 q) (meaning1583 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1573 = false ∨ valuation q 1583 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1584 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1584)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 2 4 (meaning1549 q) (meaning1574 q) (meaning1584 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1574 = false ∨ valuation q 1584 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1585 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1585)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 2 5 (meaning1549 q) (meaning1575 q) (meaning1585 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1575 = false ∨ valuation q 1585 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1586 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1586)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 2 6 (meaning1549 q) (meaning1576 q) (meaning1586 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1576 = false ∨ valuation q 1586 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1587 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1587)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 2 7 (meaning1549 q) (meaning1577 q) (meaning1587 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1577 = false ∨ valuation q 1587 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1583 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1583)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 3 2 (meaning1550 q) (meaning1572 q) (meaning1583 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1572 = false ∨ valuation q 1583 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1584 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1584)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 3 3 (meaning1550 q) (meaning1573 q) (meaning1584 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1573 = false ∨ valuation q 1584 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1585 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1585)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 3 4 (meaning1550 q) (meaning1574 q) (meaning1585 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1574 = false ∨ valuation q 1585 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1586 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1586)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 3 5 (meaning1550 q) (meaning1575 q) (meaning1586 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1575 = false ∨ valuation q 1586 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1587 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1587)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 3 6 (meaning1550 q) (meaning1576 q) (meaning1587 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1576 = false ∨ valuation q 1587 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1588 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1588)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 3 7 (meaning1550 q) (meaning1577 q) (meaning1588 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1577 = false ∨ valuation q 1588 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1584 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1584)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 4 2 (meaning1551 q) (meaning1572 q) (meaning1584 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1572 = false ∨ valuation q 1584 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1585 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1585)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 4 3 (meaning1551 q) (meaning1573 q) (meaning1585 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1573 = false ∨ valuation q 1585 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1586 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1586)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 4 4 (meaning1551 q) (meaning1574 q) (meaning1586 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1574 = false ∨ valuation q 1586 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1587 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1587)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 4 5 (meaning1551 q) (meaning1575 q) (meaning1587 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1575 = false ∨ valuation q 1587 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1588 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1588)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 4 6 (meaning1551 q) (meaning1576 q) (meaning1588 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1576 = false ∨ valuation q 1588 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1589 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1589)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 4 7 (meaning1551 q) (meaning1577 q) (meaning1589 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1577 = false ∨ valuation q 1589 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1585 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1585)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 5 2 (meaning1552 q) (meaning1572 q) (meaning1585 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1572 = false ∨ valuation q 1585 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1586 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1586)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 5 3 (meaning1552 q) (meaning1573 q) (meaning1586 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1573 = false ∨ valuation q 1586 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1587 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1587)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 5 4 (meaning1552 q) (meaning1574 q) (meaning1587 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1574 = false ∨ valuation q 1587 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1588 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1588)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 5 5 (meaning1552 q) (meaning1575 q) (meaning1588 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1575 = false ∨ valuation q 1588 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1586 = true := by
  have hs : count1579 q = (countLit q [-59, -60, -62, -65, -66, -68, -70]) + (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -62, -65, -66, -68, -70]) (l₂ := [-72, -74, -76, -78, -81, -82, -83, -86])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1572)) (literal (valuationOf q) (1586)) (countLit q [-59, -60, -62, -65, -66, -68, -70]) (countLit q [-72, -74, -76, -78, -81, -82, -83, -86]) (count1579 q) 6 2 (meaning1553 q) (meaning1572 q) (meaning1586 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1572 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1572 = false ∨ valuation q 1586 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E064.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112064
