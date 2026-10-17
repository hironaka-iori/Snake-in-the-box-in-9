import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1579)) (countLit q [-44]) (countLit q [-45]) (count1579 q) 1 (meaningNeg45 q) (meaning1579 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1579 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1579)) (countLit q [-44]) (countLit q [-45]) (count1579 q) 1 (meaningNeg44 q) (meaning1579 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1579 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 45 = true ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (1580)) (countLit q [-44]) (countLit q [-45]) (count1579 q) 1 1 (meaningNeg44 q) (meaningNeg45 q) (meaning1580 q) hs
  change (! (valuationOf q 44)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 45 = true ∨ valuation q 1580 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1581 = true := by
  have hs : count1581 q = (countLit q [-40, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-44, -45])
  have hm := merge_right (literal (valuationOf q) (1579)) (literal (valuationOf q) (1581)) (countLit q [-40, -41]) (countLit q [-44, -45]) (count1581 q) 1 (meaning1579 q) (meaning1581 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1581 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1582 = true := by
  have hs : count1581 q = (countLit q [-40, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-44, -45])
  have hm := merge_right (literal (valuationOf q) (1580)) (literal (valuationOf q) (1582)) (countLit q [-40, -41]) (countLit q [-44, -45]) (count1581 q) 2 (meaning1580 q) (meaning1582 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1582 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1581 = true := by
  have hs : count1581 q = (countLit q [-40, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-44, -45])
  have hm := merge_left (literal (valuationOf q) (1577)) (literal (valuationOf q) (1581)) (countLit q [-40, -41]) (countLit q [-44, -45]) (count1581 q) 1 (meaning1577 q) (meaning1581 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1581 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1582 = true := by
  have hs : count1581 q = (countLit q [-40, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1582)) (countLit q [-40, -41]) (countLit q [-44, -45]) (count1581 q) 1 1 (meaning1577 q) (meaning1579 q) (meaning1582 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1579 = false ∨ valuation q 1582 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1583 = true := by
  have hs : count1581 q = (countLit q [-40, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1583)) (countLit q [-40, -41]) (countLit q [-44, -45]) (count1581 q) 1 2 (meaning1577 q) (meaning1580 q) (meaning1583 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1580 = false ∨ valuation q 1583 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1582 = true := by
  have hs : count1581 q = (countLit q [-40, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-44, -45])
  have hm := merge_left (literal (valuationOf q) (1578)) (literal (valuationOf q) (1582)) (countLit q [-40, -41]) (countLit q [-44, -45]) (count1581 q) 2 (meaning1578 q) (meaning1582 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1582 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1583 = true := by
  have hs : count1581 q = (countLit q [-40, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1583)) (countLit q [-40, -41]) (countLit q [-44, -45]) (count1581 q) 2 1 (meaning1578 q) (meaning1579 q) (meaning1583 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1579 = false ∨ valuation q 1583 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1584 = true := by
  have hs : count1581 q = (countLit q [-40, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -41]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1584)) (countLit q [-40, -41]) (countLit q [-44, -45]) (count1581 q) 2 2 (meaning1578 q) (meaning1580 q) (meaning1584 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1580 = false ∨ valuation q 1584 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1585)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 1 (meaning1581 q) (meaning1585 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1585 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_right (literal (valuationOf q) (1582)) (literal (valuationOf q) (1586)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 2 (meaning1582 q) (meaning1586 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1586 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1587 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_right (literal (valuationOf q) (1583)) (literal (valuationOf q) (1587)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 3 (meaning1583 q) (meaning1587 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1587 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1588 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_right (literal (valuationOf q) (1584)) (literal (valuationOf q) (1588)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 4 (meaning1584 q) (meaning1588 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1588 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_left (literal (valuationOf q) (1574)) (literal (valuationOf q) (1585)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 1 (meaning1574 q) (meaning1585 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1585 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1586)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 1 1 (meaning1574 q) (meaning1581 q) (meaning1586 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1581 = false ∨ valuation q 1586 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1587 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1587)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 1 2 (meaning1574 q) (meaning1582 q) (meaning1587 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1582 = false ∨ valuation q 1587 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1588 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1588)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 1 3 (meaning1574 q) (meaning1583 q) (meaning1588 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1583 = false ∨ valuation q 1588 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_left (literal (valuationOf q) (1575)) (literal (valuationOf q) (1586)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 2 (meaning1575 q) (meaning1586 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1586 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1587 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1587)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 2 1 (meaning1575 q) (meaning1581 q) (meaning1587 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1581 = false ∨ valuation q 1587 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1588 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1588)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 2 2 (meaning1575 q) (meaning1582 q) (meaning1588 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1582 = false ∨ valuation q 1588 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1587 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_left (literal (valuationOf q) (1576)) (literal (valuationOf q) (1587)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 3 (meaning1576 q) (meaning1587 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1587 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1588 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1588)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 3 1 (meaning1576 q) (meaning1581 q) (meaning1588 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1581 = false ∨ valuation q 1588 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1589 = true := by
  have hs : count1585 q = (countLit q [-33, -35, -37]) + (countLit q [-40, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-40, -41, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1589)) (countLit q [-33, -35, -37]) (countLit q [-40, -41, -44, -45]) (count1585 q) 3 2 (meaning1576 q) (meaning1582 q) (meaning1589 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1582 = false ∨ valuation q 1589 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1592 = true := by
  have hs : count1592 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1592)) (countLit q [-48]) (countLit q [-49]) (count1592 q) 1 (meaningNeg49 q) (meaning1592 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1592 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1592 = true := by
  have hs : count1592 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1592)) (countLit q [-48]) (countLit q [-49]) (count1592 q) 1 (meaningNeg48 q) (meaning1592 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1592 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 49 = true ∨ valuationOf q 1593 = true := by
  have hs : count1592 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (1593)) (countLit q [-48]) (countLit q [-49]) (count1592 q) 1 1 (meaningNeg48 q) (meaningNeg49 q) (meaning1593 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 1593 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1594 = true := by
  have hs : count1594 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1594)) (countLit q [-52]) (countLit q [-54]) (count1594 q) 1 (meaningNeg54 q) (meaning1594 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1594 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1594 = true := by
  have hs : count1594 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1594)) (countLit q [-52]) (countLit q [-54]) (count1594 q) 1 (meaningNeg52 q) (meaning1594 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1594 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1595 = true := by
  have hs : count1594 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1595)) (countLit q [-52]) (countLit q [-54]) (count1594 q) 1 1 (meaningNeg52 q) (meaningNeg54 q) (meaning1595 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 1595 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-48, -49]) + (countLit q [-52, -54]) := List.countP_append (p := literal q) (l₁ := [-48, -49]) (l₂ := [-52, -54])
  have hm := merge_right (literal (valuationOf q) (1594)) (literal (valuationOf q) (1596)) (countLit q [-48, -49]) (countLit q [-52, -54]) (count1596 q) 1 (meaning1594 q) (meaning1596 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1596 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E105.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112105
