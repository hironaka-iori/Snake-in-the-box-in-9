import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 33 = true ∨ valuationOf q 1608 = true := by
  have hs : count1607 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (1608)) (countLit q [-30]) (countLit q [-33]) (count1607 q) 1 1 (meaningNeg30 q) (meaningNeg33 q) (meaning1608 q) hs
  change (! (valuationOf q 30)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 33 = true ∨ valuation q 1608 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1609 = true := by
  have hs : count1609 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (1609)) (countLit q [-35]) (countLit q [-36]) (count1609 q) 1 (meaningNeg36 q) (meaning1609 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1609 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1609 = true := by
  have hs : count1609 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (1609)) (countLit q [-35]) (countLit q [-36]) (count1609 q) 1 (meaningNeg35 q) (meaning1609 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1609 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 36 = true ∨ valuationOf q 1610 = true := by
  have hs : count1609 q = (countLit q [-35]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (1610)) (countLit q [-35]) (countLit q [-36]) (count1609 q) 1 1 (meaningNeg35 q) (meaningNeg36 q) (meaning1610 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 36 = true ∨ valuation q 1610 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1611 = true := by
  have hs : count1611 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_right (literal (valuationOf q) (1609)) (literal (valuationOf q) (1611)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1611 q) 1 (meaning1609 q) (meaning1611 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1611 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1612 = true := by
  have hs : count1611 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_right (literal (valuationOf q) (1610)) (literal (valuationOf q) (1612)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1611 q) 2 (meaning1610 q) (meaning1612 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1612 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1611 = true := by
  have hs : count1611 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_left (literal (valuationOf q) (1607)) (literal (valuationOf q) (1611)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1611 q) 1 (meaning1607 q) (meaning1611 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1611 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1612 = true := by
  have hs : count1611 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1612)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1611 q) 1 1 (meaning1607 q) (meaning1609 q) (meaning1612 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1609 = false ∨ valuation q 1612 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true := by
  have hs : count1611 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1613)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1611 q) 1 2 (meaning1607 q) (meaning1610 q) (meaning1613 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1610 = false ∨ valuation q 1613 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1612 = true := by
  have hs : count1611 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_left (literal (valuationOf q) (1608)) (literal (valuationOf q) (1612)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1611 q) 2 (meaning1608 q) (meaning1612 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1612 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1613 = true := by
  have hs : count1611 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1613)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1611 q) 2 1 (meaning1608 q) (meaning1609 q) (meaning1613 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1609 = false ∨ valuation q 1613 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1614 = true := by
  have hs : count1611 q = (countLit q [-30, -33]) + (countLit q [-35, -36]) := List.countP_append (p := literal q) (l₁ := [-30, -33]) (l₂ := [-35, -36])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1614)) (countLit q [-30, -33]) (countLit q [-35, -36]) (count1611 q) 2 2 (meaning1608 q) (meaning1610 q) (meaning1614 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1610 = false ∨ valuation q 1614 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1615 = true := by
  have hs : count1615 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1615)) (countLit q [-39]) (countLit q [-42]) (count1615 q) 1 (meaningNeg42 q) (meaning1615 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1615 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1615 = true := by
  have hs : count1615 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1615)) (countLit q [-39]) (countLit q [-42]) (count1615 q) 1 (meaningNeg39 q) (meaning1615 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1615 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1616 = true := by
  have hs : count1615 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1616)) (countLit q [-39]) (countLit q [-42]) (count1615 q) 1 1 (meaningNeg39 q) (meaningNeg42 q) (meaning1616 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 42 = true ∨ valuation q 1616 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1617)) (countLit q [-43]) (countLit q [-45]) (count1617 q) 1 (meaningNeg45 q) (meaning1617 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1617 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1617)) (countLit q [-43]) (countLit q [-45]) (count1617 q) 1 (meaningNeg43 q) (meaning1617 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1617 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 45 = true ∨ valuationOf q 1618 = true := by
  have hs : count1617 q = (countLit q [-43]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (1618)) (countLit q [-43]) (countLit q [-45]) (count1617 q) 1 1 (meaningNeg43 q) (meaningNeg45 q) (meaning1618 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 45 = true ∨ valuation q 1618 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_right (literal (valuationOf q) (1617)) (literal (valuationOf q) (1619)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1619 q) 1 (meaning1617 q) (meaning1619 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1619 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_left (literal (valuationOf q) (1615)) (literal (valuationOf q) (1619)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1619 q) 1 (meaning1615 q) (meaning1619 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1619 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1620)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1619 q) 1 1 (meaning1615 q) (meaning1617 q) (meaning1620 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1617 = false ∨ valuation q 1620 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1621 = true := by
  have hs : count1619 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1621)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1619 q) 1 2 (meaning1615 q) (meaning1618 q) (meaning1621 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1618 = false ∨ valuation q 1621 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_left (literal (valuationOf q) (1616)) (literal (valuationOf q) (1620)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1619 q) 2 (meaning1616 q) (meaning1620 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1620 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1621 = true := by
  have hs : count1619 q = (countLit q [-39, -42]) + (countLit q [-43, -45]) := List.countP_append (p := literal q) (l₁ := [-39, -42]) (l₂ := [-43, -45])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1621)) (countLit q [-39, -42]) (countLit q [-43, -45]) (count1619 q) 2 1 (meaning1616 q) (meaning1617 q) (meaning1621 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1617 = false ∨ valuation q 1621 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_right (literal (valuationOf q) (1619)) (literal (valuationOf q) (1623)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 1 (meaning1619 q) (meaning1623 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1623 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_right (literal (valuationOf q) (1620)) (literal (valuationOf q) (1624)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 2 (meaning1620 q) (meaning1624 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1624 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_right (literal (valuationOf q) (1621)) (literal (valuationOf q) (1625)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 3 (meaning1621 q) (meaning1625 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1625 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_left (literal (valuationOf q) (1611)) (literal (valuationOf q) (1623)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 1 (meaning1611 q) (meaning1623 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1623 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1624)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 1 1 (meaning1611 q) (meaning1619 q) (meaning1624 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1619 = false ∨ valuation q 1624 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1625)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 1 2 (meaning1611 q) (meaning1620 q) (meaning1625 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1620 = false ∨ valuation q 1625 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1626)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 1 3 (meaning1611 q) (meaning1621 q) (meaning1626 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1621 = false ∨ valuation q 1626 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_left (literal (valuationOf q) (1612)) (literal (valuationOf q) (1624)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1623 q) 2 (meaning1612 q) (meaning1624 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1624 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E052.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112052
