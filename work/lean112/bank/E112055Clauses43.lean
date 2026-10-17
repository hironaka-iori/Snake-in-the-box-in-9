import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1611 = true := by
  have hs : count1607 q = (countLit q [-16, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1611)) (countLit q [-16, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count1607 q) 3 2 (meaning1597 q) (meaning1604 q) (meaning1611 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1604 = false ∨ valuation q 1611 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1610 = true := by
  have hs : count1607 q = (countLit q [-16, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1598)) (literal (valuationOf q) (1610)) (countLit q [-16, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count1607 q) 4 (meaning1598 q) (meaning1610 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1610 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1611 = true := by
  have hs : count1607 q = (countLit q [-16, -18, -20, -21]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -20, -21]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1611)) (countLit q [-16, -18, -20, -21]) (countLit q [-23, -24, -27, -29]) (count1607 q) 4 1 (meaning1598 q) (meaning1603 q) (meaning1611 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1603 = false ∨ valuation q 1611 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1616 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1616)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 1 1 (meaning1584 q) (meaning1607 q) (meaning1616 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1607 = false ∨ valuation q 1616 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1617 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1617)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 1 2 (meaning1584 q) (meaning1608 q) (meaning1617 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1608 = false ∨ valuation q 1617 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1618 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1618)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 1 3 (meaning1584 q) (meaning1609 q) (meaning1618 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1609 = false ∨ valuation q 1618 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1619 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1619)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 1 4 (meaning1584 q) (meaning1610 q) (meaning1619 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1610 = false ∨ valuation q 1619 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1620 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1620)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 1 5 (meaning1584 q) (meaning1611 q) (meaning1620 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1611 = false ∨ valuation q 1620 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1617 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1617)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 2 1 (meaning1585 q) (meaning1607 q) (meaning1617 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1607 = false ∨ valuation q 1617 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1618 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1618)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 2 2 (meaning1585 q) (meaning1608 q) (meaning1618 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1608 = false ∨ valuation q 1618 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1619 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1619)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 2 3 (meaning1585 q) (meaning1609 q) (meaning1619 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1609 = false ∨ valuation q 1619 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1620 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1620)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 2 4 (meaning1585 q) (meaning1610 q) (meaning1620 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1610 = false ∨ valuation q 1620 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1621 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1621)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 2 5 (meaning1585 q) (meaning1611 q) (meaning1621 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1611 = false ∨ valuation q 1621 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1618 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1618)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 3 1 (meaning1586 q) (meaning1607 q) (meaning1618 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1607 = false ∨ valuation q 1618 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1619 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1619)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 3 2 (meaning1586 q) (meaning1608 q) (meaning1619 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1608 = false ∨ valuation q 1619 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1620 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1620)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 3 3 (meaning1586 q) (meaning1609 q) (meaning1620 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1609 = false ∨ valuation q 1620 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1621 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1621)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 3 4 (meaning1586 q) (meaning1610 q) (meaning1621 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1610 = false ∨ valuation q 1621 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1622 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1622)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 3 5 (meaning1586 q) (meaning1611 q) (meaning1622 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1611 = false ∨ valuation q 1622 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1619 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1619)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 4 1 (meaning1587 q) (meaning1607 q) (meaning1619 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1607 = false ∨ valuation q 1619 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1620 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1620)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 4 2 (meaning1587 q) (meaning1608 q) (meaning1620 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1608 = false ∨ valuation q 1620 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1621 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1621)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 4 3 (meaning1587 q) (meaning1609 q) (meaning1621 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1609 = false ∨ valuation q 1621 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1622 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1622)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 4 4 (meaning1587 q) (meaning1610 q) (meaning1622 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1610 = false ∨ valuation q 1622 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1620 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1620)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 5 1 (meaning1588 q) (meaning1607 q) (meaning1620 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1607 = false ∨ valuation q 1620 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1621 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1621)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 5 2 (meaning1588 q) (meaning1608 q) (meaning1621 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1608 = false ∨ valuation q 1621 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1622 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1622)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 5 3 (meaning1588 q) (meaning1609 q) (meaning1622 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1609 = false ∨ valuation q 1622 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1623 = true := by
  have hs : count1615 q = (countLit q [-2, -3, -5, -8, -12, -13, -14]) + (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14]) (l₂ := [-16, -18, -20, -21, -23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1623)) (countLit q [-2, -3, -5, -8, -12, -13, -14]) (countLit q [-16, -18, -20, -21, -23, -24, -27, -29]) (count1615 q) 5 4 (meaning1588 q) (meaning1610 q) (meaning1623 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1610 = false ∨ valuation q 1623 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-31]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32])
  have hm := merge_right (literal (valuationOf q) (-32)) (literal (valuationOf q) (1630)) (countLit q [-31]) (countLit q [-32]) (count1630 q) 1 (meaningNeg32 q) (meaning1630 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1630 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-31]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1630)) (countLit q [-31]) (countLit q [-32]) (count1630 q) 1 (meaningNeg31 q) (meaning1630 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1630 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 32 = true ∨ valuationOf q 1631 = true := by
  have hs : count1630 q = (countLit q [-31]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (-32)) (literal (valuationOf q) (1631)) (countLit q [-31]) (countLit q [-32]) (count1630 q) 1 1 (meaningNeg31 q) (meaningNeg32 q) (meaning1631 q) hs
  change (! (valuationOf q 31)) = false ∨ (! (valuationOf q 32)) = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 32 = true ∨ valuation q 1631 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-34]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1632)) (countLit q [-34]) (countLit q [-37]) (count1632 q) 1 (meaningNeg37 q) (meaning1632 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1632 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-34]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1632)) (countLit q [-34]) (countLit q [-37]) (count1632 q) 1 (meaningNeg34 q) (meaning1632 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1632 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-34]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1633)) (countLit q [-34]) (countLit q [-37]) (count1632 q) 1 1 (meaningNeg34 q) (meaningNeg37 q) (meaning1633 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 37 = true ∨ valuation q 1633 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E055.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112055
