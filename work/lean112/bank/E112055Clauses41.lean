import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-8, -12]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -12]) (l₂ := [-13, -14])
  have hm := merge_left (literal (valuationOf q) (1576)) (literal (valuationOf q) (1580)) (countLit q [-8, -12]) (countLit q [-13, -14]) (count1580 q) 1 (meaning1576 q) (meaning1580 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1580 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-8, -12]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -12]) (l₂ := [-13, -14])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1581)) (countLit q [-8, -12]) (countLit q [-13, -14]) (count1580 q) 1 1 (meaning1576 q) (meaning1578 q) (meaning1581 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1578 = false ∨ valuation q 1581 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1582 = true := by
  have hs : count1580 q = (countLit q [-8, -12]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -12]) (l₂ := [-13, -14])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1582)) (countLit q [-8, -12]) (countLit q [-13, -14]) (count1580 q) 1 2 (meaning1576 q) (meaning1579 q) (meaning1582 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1579 = false ∨ valuation q 1582 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-8, -12]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -12]) (l₂ := [-13, -14])
  have hm := merge_left (literal (valuationOf q) (1577)) (literal (valuationOf q) (1581)) (countLit q [-8, -12]) (countLit q [-13, -14]) (count1580 q) 2 (meaning1577 q) (meaning1581 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1581 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1582 = true := by
  have hs : count1580 q = (countLit q [-8, -12]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -12]) (l₂ := [-13, -14])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1582)) (countLit q [-8, -12]) (countLit q [-13, -14]) (count1580 q) 2 1 (meaning1577 q) (meaning1578 q) (meaning1582 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1578 = false ∨ valuation q 1582 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1583 = true := by
  have hs : count1580 q = (countLit q [-8, -12]) + (countLit q [-13, -14]) := List.countP_append (p := literal q) (l₁ := [-8, -12]) (l₂ := [-13, -14])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1583)) (countLit q [-8, -12]) (countLit q [-13, -14]) (count1580 q) 2 2 (meaning1577 q) (meaning1579 q) (meaning1583 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1579 = false ∨ valuation q 1583 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1584 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_right (literal (valuationOf q) (1580)) (literal (valuationOf q) (1584)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 1 (meaning1580 q) (meaning1584 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1584 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1585)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 2 (meaning1581 q) (meaning1585 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1585 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1586 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_right (literal (valuationOf q) (1582)) (literal (valuationOf q) (1586)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 3 (meaning1582 q) (meaning1586 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1586 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1587 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_right (literal (valuationOf q) (1583)) (literal (valuationOf q) (1587)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 4 (meaning1583 q) (meaning1587 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1587 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1584 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_left (literal (valuationOf q) (1573)) (literal (valuationOf q) (1584)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 1 (meaning1573 q) (meaning1584 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1584 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1585)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 1 1 (meaning1573 q) (meaning1580 q) (meaning1585 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1580 = false ∨ valuation q 1585 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1586 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1586)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 1 2 (meaning1573 q) (meaning1581 q) (meaning1586 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1581 = false ∨ valuation q 1586 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1587 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1587)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 1 3 (meaning1573 q) (meaning1582 q) (meaning1587 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1582 = false ∨ valuation q 1587 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1588 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1588)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 1 4 (meaning1573 q) (meaning1583 q) (meaning1588 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1583 = false ∨ valuation q 1588 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_left (literal (valuationOf q) (1574)) (literal (valuationOf q) (1585)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 2 (meaning1574 q) (meaning1585 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1585 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1586 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1586)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 2 1 (meaning1574 q) (meaning1580 q) (meaning1586 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1580 = false ∨ valuation q 1586 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1587 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1587)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 2 2 (meaning1574 q) (meaning1581 q) (meaning1587 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1581 = false ∨ valuation q 1587 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1588 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1588)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 2 3 (meaning1574 q) (meaning1582 q) (meaning1588 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1582 = false ∨ valuation q 1588 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1586 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_left (literal (valuationOf q) (1575)) (literal (valuationOf q) (1586)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 3 (meaning1575 q) (meaning1586 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1586 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1587 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1587)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 3 1 (meaning1575 q) (meaning1580 q) (meaning1587 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1580 = false ∨ valuation q 1587 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1588 = true := by
  have hs : count1584 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -12, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -12, -13, -14])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1588)) (countLit q [-2, -3, -5]) (countLit q [-8, -12, -13, -14]) (count1584 q) 3 2 (meaning1575 q) (meaning1581 q) (meaning1588 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1581 = false ∨ valuation q 1588 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1591)) (countLit q [-16]) (countLit q [-18]) (count1591 q) 1 (meaningNeg18 q) (meaning1591 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1591 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1591)) (countLit q [-16]) (countLit q [-18]) (count1591 q) 1 (meaningNeg16 q) (meaning1591 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1591 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 18 = true ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (1592)) (countLit q [-16]) (countLit q [-18]) (count1591 q) 1 1 (meaningNeg16 q) (meaningNeg18 q) (meaning1592 q) hs
  change (! (valuationOf q 16)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 18 = true ∨ valuation q 1592 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1593)) (countLit q [-20]) (countLit q [-21]) (count1593 q) 1 (meaningNeg21 q) (meaning1593 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1593 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1593)) (countLit q [-20]) (countLit q [-21]) (count1593 q) 1 (meaningNeg20 q) (meaning1593 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1593 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 21 = true ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (1594)) (countLit q [-20]) (countLit q [-21]) (count1593 q) 1 1 (meaningNeg20 q) (meaningNeg21 q) (meaning1594 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 1594 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1595 = true := by
  have hs : count1595 q = (countLit q [-16, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-16, -18]) (l₂ := [-20, -21])
  have hm := merge_right (literal (valuationOf q) (1593)) (literal (valuationOf q) (1595)) (countLit q [-16, -18]) (countLit q [-20, -21]) (count1595 q) 1 (meaning1593 q) (meaning1595 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1595 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1596 = true := by
  have hs : count1595 q = (countLit q [-16, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-16, -18]) (l₂ := [-20, -21])
  have hm := merge_right (literal (valuationOf q) (1594)) (literal (valuationOf q) (1596)) (countLit q [-16, -18]) (countLit q [-20, -21]) (count1595 q) 2 (meaning1594 q) (meaning1596 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1596 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1595 = true := by
  have hs : count1595 q = (countLit q [-16, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-16, -18]) (l₂ := [-20, -21])
  have hm := merge_left (literal (valuationOf q) (1591)) (literal (valuationOf q) (1595)) (countLit q [-16, -18]) (countLit q [-20, -21]) (count1595 q) 1 (meaning1591 q) (meaning1595 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1595 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1596 = true := by
  have hs : count1595 q = (countLit q [-16, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-16, -18]) (l₂ := [-20, -21])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1596)) (countLit q [-16, -18]) (countLit q [-20, -21]) (count1595 q) 1 1 (meaning1591 q) (meaning1593 q) (meaning1596 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1593 = false ∨ valuation q 1596 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E055.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112055
