import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1639 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1639)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 3 1 (meaning1627 q) (meaning1632 q) (meaning1639 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1632 = false ∨ valuation q 1639 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1640 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1640)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 3 2 (meaning1627 q) (meaning1633 q) (meaning1640 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1633 = false ∨ valuation q 1640 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1641 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1641)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 3 3 (meaning1627 q) (meaning1634 q) (meaning1641 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1634 = false ∨ valuation q 1641 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-108]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-110])
  have hm := merge_right (literal (valuationOf q) (-110)) (literal (valuationOf q) (1643)) (countLit q [-108]) (countLit q [-110]) (count1643 q) 1 (meaningNeg110 q) (meaning1643 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1643 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-108]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-108)) (literal (valuationOf q) (1643)) (countLit q [-108]) (countLit q [-110]) (count1643 q) 1 (meaningNeg108 q) (meaning1643 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1643 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 110 = true ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-108]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-108]) (l₂ := [-110])
  have hm := merge_two (literal (valuationOf q) (-108)) (literal (valuationOf q) (-110)) (literal (valuationOf q) (1644)) (countLit q [-108]) (countLit q [-110]) (count1643 q) 1 1 (meaningNeg108 q) (meaningNeg110 q) (meaning1644 q) hs
  change (! (valuationOf q 108)) = false ∨ (! (valuationOf q 110)) = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 110 = true ∨ valuation q 1644 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-105]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108, -110])
  have hm := merge_right (literal (valuationOf q) (1643)) (literal (valuationOf q) (1645)) (countLit q [-105]) (countLit q [-108, -110]) (count1645 q) 1 (meaning1643 q) (meaning1645 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1645 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-105]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108, -110])
  have hm := merge_right (literal (valuationOf q) (1644)) (literal (valuationOf q) (1646)) (countLit q [-105]) (countLit q [-108, -110]) (count1645 q) 2 (meaning1644 q) (meaning1646 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1646 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-105]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108, -110])
  have hm := merge_left (literal (valuationOf q) (-105)) (literal (valuationOf q) (1645)) (countLit q [-105]) (countLit q [-108, -110]) (count1645 q) 1 (meaningNeg105 q) (meaning1645 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1645 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1643 = false ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-105]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108, -110])
  have hm := merge_two (literal (valuationOf q) (-105)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1646)) (countLit q [-105]) (countLit q [-108, -110]) (count1645 q) 1 1 (meaningNeg105 q) (meaning1643 q) (meaning1646 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1643 = false ∨ valuation q 1646 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1644 = false ∨ valuationOf q 1647 = true := by
  have hs : count1645 q = (countLit q [-105]) + (countLit q [-108, -110]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108, -110])
  have hm := merge_two (literal (valuationOf q) (-105)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1647)) (countLit q [-105]) (countLit q [-108, -110]) (count1645 q) 1 2 (meaningNeg105 q) (meaning1644 q) (meaning1647 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1644 = false ∨ valuation q 1647 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1648 = true := by
  have hs : count1648 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1648)) (countLit q [-111]) (countLit q [-113]) (count1648 q) 1 (meaningNeg113 q) (meaning1648 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1648 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1648 = true := by
  have hs : count1648 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1648)) (countLit q [-111]) (countLit q [-113]) (count1648 q) 1 (meaningNeg111 q) (meaning1648 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1648 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1649 = true := by
  have hs : count1648 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1649)) (countLit q [-111]) (countLit q [-113]) (count1648 q) 1 1 (meaningNeg111 q) (meaningNeg113 q) (meaning1649 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 1649 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_right (literal (valuationOf q) (-117)) (literal (valuationOf q) (1650)) (countLit q [-115]) (countLit q [-117]) (count1650 q) 1 (meaningNeg117 q) (meaning1650 q) hs
  change (! (valuationOf q 117)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 1650 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1650)) (countLit q [-115]) (countLit q [-117]) (count1650 q) 1 (meaningNeg115 q) (meaning1650 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1650 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 117 = true ∨ valuationOf q 1651 = true := by
  have hs : count1650 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-117)) (literal (valuationOf q) (1651)) (countLit q [-115]) (countLit q [-117]) (count1650 q) 1 1 (meaningNeg115 q) (meaningNeg117 q) (meaning1651 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 117)) = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 1651 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1650)) (literal (valuationOf q) (1652)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1652 q) 1 (meaning1650 q) (meaning1652 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1652 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1651)) (literal (valuationOf q) (1653)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1652 q) 2 (meaning1651 q) (meaning1653 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1653 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1648)) (literal (valuationOf q) (1652)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1652 q) 1 (meaning1648 q) (meaning1652 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1652 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1653)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1652 q) 1 1 (meaning1648 q) (meaning1650 q) (meaning1653 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1650 = false ∨ valuation q 1653 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1654 = true := by
  have hs : count1652 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1654)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1652 q) 1 2 (meaning1648 q) (meaning1651 q) (meaning1654 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1651 = false ∨ valuation q 1654 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1649)) (literal (valuationOf q) (1653)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1652 q) 2 (meaning1649 q) (meaning1653 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1653 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1654 = true := by
  have hs : count1652 q = (countLit q [-111, -113]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -113]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1654)) (countLit q [-111, -113]) (countLit q [-115, -117]) (count1652 q) 2 1 (meaning1649 q) (meaning1650 q) (meaning1654 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1650 = false ∨ valuation q 1654 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1656 = true := by
  have hs : count1656 q = (countLit q [-105, -108, -110]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1652)) (literal (valuationOf q) (1656)) (countLit q [-105, -108, -110]) (countLit q [-111, -113, -115, -117]) (count1656 q) 1 (meaning1652 q) (meaning1656 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1656 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1657 = true := by
  have hs : count1656 q = (countLit q [-105, -108, -110]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1653)) (literal (valuationOf q) (1657)) (countLit q [-105, -108, -110]) (countLit q [-111, -113, -115, -117]) (count1656 q) 2 (meaning1653 q) (meaning1657 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1657 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1658 = true := by
  have hs : count1656 q = (countLit q [-105, -108, -110]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1654)) (literal (valuationOf q) (1658)) (countLit q [-105, -108, -110]) (countLit q [-111, -113, -115, -117]) (count1656 q) 3 (meaning1654 q) (meaning1658 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1658 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1657 = true := by
  have hs : count1656 q = (countLit q [-105, -108, -110]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1657)) (countLit q [-105, -108, -110]) (countLit q [-111, -113, -115, -117]) (count1656 q) 1 1 (meaning1645 q) (meaning1652 q) (meaning1657 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1652 = false ∨ valuation q 1657 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1658 = true := by
  have hs : count1656 q = (countLit q [-105, -108, -110]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1658)) (countLit q [-105, -108, -110]) (countLit q [-111, -113, -115, -117]) (count1656 q) 1 2 (meaning1645 q) (meaning1653 q) (meaning1658 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1653 = false ∨ valuation q 1658 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1659 = true := by
  have hs : count1656 q = (countLit q [-105, -108, -110]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1659)) (countLit q [-105, -108, -110]) (countLit q [-111, -113, -115, -117]) (count1656 q) 1 3 (meaning1645 q) (meaning1654 q) (meaning1659 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1654 = false ∨ valuation q 1659 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1658 = true := by
  have hs : count1656 q = (countLit q [-105, -108, -110]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1658)) (countLit q [-105, -108, -110]) (countLit q [-111, -113, -115, -117]) (count1656 q) 2 1 (meaning1646 q) (meaning1652 q) (meaning1658 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1652 = false ∨ valuation q 1658 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1659 = true := by
  have hs : count1656 q = (countLit q [-105, -108, -110]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1659)) (countLit q [-105, -108, -110]) (countLit q [-111, -113, -115, -117]) (count1656 q) 2 2 (meaning1646 q) (meaning1653 q) (meaning1659 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1653 = false ∨ valuation q 1659 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E047.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112047
