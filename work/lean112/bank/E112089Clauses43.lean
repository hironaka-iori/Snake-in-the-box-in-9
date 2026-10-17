import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1543 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1543)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 2 1 (meaning1530 q) (meaning1537 q) (meaning1543 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1537 = false ∨ valuation q 1543 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1544)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 2 2 (meaning1530 q) (meaning1538 q) (meaning1544 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1538 = false ∨ valuation q 1544 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1545)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 2 3 (meaning1530 q) (meaning1539 q) (meaning1545 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1539 = false ∨ valuation q 1545 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1543 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1531)) (literal (valuationOf q) (1543)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 3 (meaning1531 q) (meaning1543 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1543 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1544)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 3 1 (meaning1531 q) (meaning1537 q) (meaning1544 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1537 = false ∨ valuation q 1544 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1545)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 3 2 (meaning1531 q) (meaning1538 q) (meaning1545 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1538 = false ∨ valuation q 1545 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1546)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 3 3 (meaning1531 q) (meaning1539 q) (meaning1546 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1539 = false ∨ valuation q 1546 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1532)) (literal (valuationOf q) (1544)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 4 (meaning1532 q) (meaning1544 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1544 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1545)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 4 1 (meaning1532 q) (meaning1537 q) (meaning1545 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1537 = false ∨ valuation q 1545 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-14, -15, -18, -22]) + (countLit q [-24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-14, -15, -18, -22]) (l₂ := [-24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1547)) (countLit q [-14, -15, -18, -22]) (countLit q [-24, -25, -27, -29]) (count1541 q) 4 3 (meaning1532 q) (meaning1539 q) (meaning1547 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1539 = false ∨ valuation q 1547 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1551 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1551)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 1 2 (meaning1518 q) (meaning1542 q) (meaning1551 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1542 = false ∨ valuation q 1551 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1552 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1552)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 1 3 (meaning1518 q) (meaning1543 q) (meaning1552 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1543 = false ∨ valuation q 1552 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1553 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1553)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 1 4 (meaning1518 q) (meaning1544 q) (meaning1553 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1544 = false ∨ valuation q 1553 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1554 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1554)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 1 5 (meaning1518 q) (meaning1545 q) (meaning1554 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1545 = false ∨ valuation q 1554 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1555 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1555)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 1 6 (meaning1518 q) (meaning1546 q) (meaning1555 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1546 = false ∨ valuation q 1555 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1551 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1551)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 2 1 (meaning1519 q) (meaning1541 q) (meaning1551 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1541 = false ∨ valuation q 1551 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1552 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1552)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 2 2 (meaning1519 q) (meaning1542 q) (meaning1552 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1542 = false ∨ valuation q 1552 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1553 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1553)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 2 3 (meaning1519 q) (meaning1543 q) (meaning1553 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1543 = false ∨ valuation q 1553 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1554 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1554)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 2 4 (meaning1519 q) (meaning1544 q) (meaning1554 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1544 = false ∨ valuation q 1554 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1555 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1555)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 2 5 (meaning1519 q) (meaning1545 q) (meaning1555 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1545 = false ∨ valuation q 1555 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1556 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1556)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 2 6 (meaning1519 q) (meaning1546 q) (meaning1556 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1546 = false ∨ valuation q 1556 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1557 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1557)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 2 7 (meaning1519 q) (meaning1547 q) (meaning1557 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1547 = false ∨ valuation q 1557 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1551 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1520)) (literal (valuationOf q) (1551)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 3 (meaning1520 q) (meaning1551 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1551 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1552 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1552)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 3 1 (meaning1520 q) (meaning1541 q) (meaning1552 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1541 = false ∨ valuation q 1552 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1553)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 3 2 (meaning1520 q) (meaning1542 q) (meaning1553 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1542 = false ∨ valuation q 1553 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1554 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1554)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 3 3 (meaning1520 q) (meaning1543 q) (meaning1554 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1543 = false ∨ valuation q 1554 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1555 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1555)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 3 4 (meaning1520 q) (meaning1544 q) (meaning1555 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1544 = false ∨ valuation q 1555 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1556 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1556)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 3 5 (meaning1520 q) (meaning1545 q) (meaning1556 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1545 = false ∨ valuation q 1556 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1552 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1521)) (literal (valuationOf q) (1552)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 4 (meaning1521 q) (meaning1552 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1552 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1553 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1553)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 4 1 (meaning1521 q) (meaning1541 q) (meaning1553 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1541 = false ∨ valuation q 1553 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1554)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 4 2 (meaning1521 q) (meaning1542 q) (meaning1554 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1542 = false ∨ valuation q 1554 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1555 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1555)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 4 3 (meaning1521 q) (meaning1543 q) (meaning1555 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1543 = false ∨ valuation q 1555 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E089.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112089
