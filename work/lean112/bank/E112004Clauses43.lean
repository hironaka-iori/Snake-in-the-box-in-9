import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-62]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (1580)) (countLit q [-62]) (countLit q [-64]) (count1580 q) 1 (meaningNeg64 q) (meaning1580 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1580 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-62]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (1580)) (countLit q [-62]) (countLit q [-64]) (count1580 q) 1 (meaningNeg62 q) (meaning1580 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1580 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 64 = true ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-62]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-64])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (-64)) (literal (valuationOf q) (1581)) (countLit q [-62]) (countLit q [-64]) (count1580 q) 1 1 (meaningNeg62 q) (meaningNeg64 q) (meaning1581 q) hs
  change (! (valuationOf q 62)) = false ∨ (! (valuationOf q 64)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 64 = true ∨ valuation q 1581 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-61]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -64])
  have hm := merge_right (literal (valuationOf q) (1580)) (literal (valuationOf q) (1582)) (countLit q [-61]) (countLit q [-62, -64]) (count1582 q) 1 (meaning1580 q) (meaning1582 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1582 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-61]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -64])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1583)) (countLit q [-61]) (countLit q [-62, -64]) (count1582 q) 2 (meaning1581 q) (meaning1583 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1583 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-61]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -64])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1582)) (countLit q [-61]) (countLit q [-62, -64]) (count1582 q) 1 (meaningNeg61 q) (meaning1582 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1582 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1580 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-61]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -64])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1583)) (countLit q [-61]) (countLit q [-62, -64]) (count1582 q) 1 1 (meaningNeg61 q) (meaning1580 q) (meaning1583 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1580 = false ∨ valuation q 1583 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-61]) + (countLit q [-62, -64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-62, -64])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1584)) (countLit q [-61]) (countLit q [-62, -64]) (count1582 q) 1 2 (meaningNeg61 q) (meaning1581 q) (meaning1584 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1581 = false ∨ valuation q 1584 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1585)) (countLit q [-67]) (countLit q [-70]) (count1585 q) 1 (meaningNeg70 q) (meaning1585 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1585 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1585)) (countLit q [-67]) (countLit q [-70]) (count1585 q) 1 (meaningNeg67 q) (meaning1585 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1585 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 70 = true ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-70)) (literal (valuationOf q) (1586)) (countLit q [-67]) (countLit q [-70]) (count1585 q) 1 1 (meaningNeg67 q) (meaningNeg70 q) (meaning1586 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 70)) = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 70 = true ∨ valuation q 1586 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1587)) (countLit q [-71]) (countLit q [-73]) (count1587 q) 1 (meaningNeg73 q) (meaning1587 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1587 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1587)) (countLit q [-71]) (countLit q [-73]) (count1587 q) 1 (meaningNeg71 q) (meaning1587 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1587 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1588)) (countLit q [-71]) (countLit q [-73]) (count1587 q) 1 1 (meaningNeg71 q) (meaningNeg73 q) (meaning1588 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 73 = true ∨ valuation q 1588 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-67, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (1587)) (literal (valuationOf q) (1589)) (countLit q [-67, -70]) (countLit q [-71, -73]) (count1589 q) 1 (meaning1587 q) (meaning1589 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1589 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-67, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-71, -73])
  have hm := merge_right (literal (valuationOf q) (1588)) (literal (valuationOf q) (1590)) (countLit q [-67, -70]) (countLit q [-71, -73]) (count1589 q) 2 (meaning1588 q) (meaning1590 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1590 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-67, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-71, -73])
  have hm := merge_left (literal (valuationOf q) (1585)) (literal (valuationOf q) (1589)) (countLit q [-67, -70]) (countLit q [-71, -73]) (count1589 q) 1 (meaning1585 q) (meaning1589 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1589 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-67, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1590)) (countLit q [-67, -70]) (countLit q [-71, -73]) (count1589 q) 1 1 (meaning1585 q) (meaning1587 q) (meaning1590 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1587 = false ∨ valuation q 1590 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1591 = true := by
  have hs : count1589 q = (countLit q [-67, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1591)) (countLit q [-67, -70]) (countLit q [-71, -73]) (count1589 q) 1 2 (meaning1585 q) (meaning1588 q) (meaning1591 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1588 = false ∨ valuation q 1591 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-67, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-71, -73])
  have hm := merge_left (literal (valuationOf q) (1586)) (literal (valuationOf q) (1590)) (countLit q [-67, -70]) (countLit q [-71, -73]) (count1589 q) 2 (meaning1586 q) (meaning1590 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1590 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1591 = true := by
  have hs : count1589 q = (countLit q [-67, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1591)) (countLit q [-67, -70]) (countLit q [-71, -73]) (count1589 q) 2 1 (meaning1586 q) (meaning1587 q) (meaning1591 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1587 = false ∨ valuation q 1591 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1592 = true := by
  have hs : count1589 q = (countLit q [-67, -70]) + (countLit q [-71, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-71, -73])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1592)) (countLit q [-67, -70]) (countLit q [-71, -73]) (count1589 q) 2 2 (meaning1586 q) (meaning1588 q) (meaning1592 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1588 = false ∨ valuation q 1592 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_right (literal (valuationOf q) (1589)) (literal (valuationOf q) (1593)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 1 (meaning1589 q) (meaning1593 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1593 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1594)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 2 (meaning1590 q) (meaning1594 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1594 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1595 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_right (literal (valuationOf q) (1591)) (literal (valuationOf q) (1595)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 3 (meaning1591 q) (meaning1595 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1595 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1596 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_right (literal (valuationOf q) (1592)) (literal (valuationOf q) (1596)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 4 (meaning1592 q) (meaning1596 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1596 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_left (literal (valuationOf q) (1582)) (literal (valuationOf q) (1593)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 1 (meaning1582 q) (meaning1593 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1593 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1594)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 1 1 (meaning1582 q) (meaning1589 q) (meaning1594 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1589 = false ∨ valuation q 1594 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1595 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1595)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 1 2 (meaning1582 q) (meaning1590 q) (meaning1595 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1590 = false ∨ valuation q 1595 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1596 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1596)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 1 3 (meaning1582 q) (meaning1591 q) (meaning1596 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1591 = false ∨ valuation q 1596 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_left (literal (valuationOf q) (1583)) (literal (valuationOf q) (1594)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 2 (meaning1583 q) (meaning1594 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1594 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1595 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1595)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 2 1 (meaning1583 q) (meaning1589 q) (meaning1595 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1589 = false ∨ valuation q 1595 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E004.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112004
