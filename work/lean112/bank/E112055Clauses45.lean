import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-31, -32, -34, -37]) + (countLit q [-38, -40, -41, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37]) (l₂ := [-38, -40, -41, -44])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1649)) (countLit q [-31, -32, -34, -37]) (countLit q [-38, -40, -41, -44]) (count1646 q) 3 1 (meaning1636 q) (meaning1642 q) (meaning1649 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1642 = false ∨ valuation q 1649 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-31, -32, -34, -37]) + (countLit q [-38, -40, -41, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37]) (l₂ := [-38, -40, -41, -44])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1650)) (countLit q [-31, -32, -34, -37]) (countLit q [-38, -40, -41, -44]) (count1646 q) 3 2 (meaning1636 q) (meaning1643 q) (meaning1650 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1643 = false ∨ valuation q 1650 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-31, -32, -34, -37]) + (countLit q [-38, -40, -41, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37]) (l₂ := [-38, -40, -41, -44])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1651)) (countLit q [-31, -32, -34, -37]) (countLit q [-38, -40, -41, -44]) (count1646 q) 3 3 (meaning1636 q) (meaning1644 q) (meaning1651 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1644 = false ∨ valuation q 1651 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-31, -32, -34, -37]) + (countLit q [-38, -40, -41, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37]) (l₂ := [-38, -40, -41, -44])
  have hm := merge_left (literal (valuationOf q) (1637)) (literal (valuationOf q) (1649)) (countLit q [-31, -32, -34, -37]) (countLit q [-38, -40, -41, -44]) (count1646 q) 4 (meaning1637 q) (meaning1649 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1649 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1650 = true := by
  have hs : count1646 q = (countLit q [-31, -32, -34, -37]) + (countLit q [-38, -40, -41, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37]) (l₂ := [-38, -40, -41, -44])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1650)) (countLit q [-31, -32, -34, -37]) (countLit q [-38, -40, -41, -44]) (count1646 q) 4 1 (meaning1637 q) (meaning1642 q) (meaning1650 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1642 = false ∨ valuation q 1650 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1651 = true := by
  have hs : count1646 q = (countLit q [-31, -32, -34, -37]) + (countLit q [-38, -40, -41, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37]) (l₂ := [-38, -40, -41, -44])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1651)) (countLit q [-31, -32, -34, -37]) (countLit q [-38, -40, -41, -44]) (count1646 q) 4 2 (meaning1637 q) (meaning1643 q) (meaning1651 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1643 = false ∨ valuation q 1651 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-45]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1654)) (countLit q [-45]) (countLit q [-49]) (count1654 q) 1 (meaningNeg49 q) (meaning1654 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1654 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-45]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1654)) (countLit q [-45]) (countLit q [-49]) (count1654 q) 1 (meaningNeg45 q) (meaning1654 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1654 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 49 = true ∨ valuationOf q 1655 = true := by
  have hs : count1654 q = (countLit q [-45]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (1655)) (countLit q [-45]) (countLit q [-49]) (count1654 q) 1 1 (meaningNeg45 q) (meaningNeg49 q) (meaning1655 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 49 = true ∨ valuation q 1655 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1656 = true := by
  have hs : count1656 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (1656)) (countLit q [-52]) (countLit q [-53]) (count1656 q) 1 (meaningNeg53 q) (meaning1656 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1656 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1656 = true := by
  have hs : count1656 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1656)) (countLit q [-52]) (countLit q [-53]) (count1656 q) 1 (meaningNeg52 q) (meaning1656 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1656 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 53 = true ∨ valuationOf q 1657 = true := by
  have hs : count1656 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (1657)) (countLit q [-52]) (countLit q [-53]) (count1656 q) 1 1 (meaningNeg52 q) (meaningNeg53 q) (meaning1657 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 1657 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1658 = true := by
  have hs : count1658 q = (countLit q [-45, -49]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-52, -53])
  have hm := merge_right (literal (valuationOf q) (1656)) (literal (valuationOf q) (1658)) (countLit q [-45, -49]) (countLit q [-52, -53]) (count1658 q) 1 (meaning1656 q) (meaning1658 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1658 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1659 = true := by
  have hs : count1658 q = (countLit q [-45, -49]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-52, -53])
  have hm := merge_right (literal (valuationOf q) (1657)) (literal (valuationOf q) (1659)) (countLit q [-45, -49]) (countLit q [-52, -53]) (count1658 q) 2 (meaning1657 q) (meaning1659 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1659 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1658 = true := by
  have hs : count1658 q = (countLit q [-45, -49]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-52, -53])
  have hm := merge_left (literal (valuationOf q) (1654)) (literal (valuationOf q) (1658)) (countLit q [-45, -49]) (countLit q [-52, -53]) (count1658 q) 1 (meaning1654 q) (meaning1658 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1658 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1659 = true := by
  have hs : count1658 q = (countLit q [-45, -49]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-52, -53])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1659)) (countLit q [-45, -49]) (countLit q [-52, -53]) (count1658 q) 1 1 (meaning1654 q) (meaning1656 q) (meaning1659 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1656 = false ∨ valuation q 1659 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1660 = true := by
  have hs : count1658 q = (countLit q [-45, -49]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-52, -53])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1660)) (countLit q [-45, -49]) (countLit q [-52, -53]) (count1658 q) 1 2 (meaning1654 q) (meaning1657 q) (meaning1660 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1657 = false ∨ valuation q 1660 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1659 = true := by
  have hs : count1658 q = (countLit q [-45, -49]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-52, -53])
  have hm := merge_left (literal (valuationOf q) (1655)) (literal (valuationOf q) (1659)) (countLit q [-45, -49]) (countLit q [-52, -53]) (count1658 q) 2 (meaning1655 q) (meaning1659 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1659 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1660 = true := by
  have hs : count1658 q = (countLit q [-45, -49]) + (countLit q [-52, -53]) := List.countP_append (p := literal q) (l₁ := [-45, -49]) (l₂ := [-52, -53])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1660)) (countLit q [-45, -49]) (countLit q [-52, -53]) (count1658 q) 2 1 (meaning1655 q) (meaning1656 q) (meaning1660 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1656 = false ∨ valuation q 1660 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1662 = true := by
  have hs : count1662 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (1662)) (countLit q [-55]) (countLit q [-57]) (count1662 q) 1 (meaningNeg57 q) (meaning1662 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1662 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1662 = true := by
  have hs : count1662 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1662)) (countLit q [-55]) (countLit q [-57]) (count1662 q) 1 (meaningNeg55 q) (meaning1662 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1662 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 57 = true ∨ valuationOf q 1663 = true := by
  have hs : count1662 q = (countLit q [-55]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-57])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (-57)) (literal (valuationOf q) (1663)) (countLit q [-55]) (countLit q [-57]) (count1662 q) 1 1 (meaningNeg55 q) (meaningNeg57 q) (meaning1663 q) hs
  change (! (valuationOf q 55)) = false ∨ (! (valuationOf q 57)) = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 57 = true ∨ valuation q 1663 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1664 = true := by
  have hs : count1664 q = (countLit q [-58]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (1664)) (countLit q [-58]) (countLit q [-62]) (count1664 q) 1 (meaningNeg62 q) (meaning1664 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1664 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1664 = true := by
  have hs : count1664 q = (countLit q [-58]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1664)) (countLit q [-58]) (countLit q [-62]) (count1664 q) 1 (meaningNeg58 q) (meaning1664 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1664 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 62 = true ∨ valuationOf q 1665 = true := by
  have hs : count1664 q = (countLit q [-58]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (1665)) (countLit q [-58]) (countLit q [-62]) (count1664 q) 1 1 (meaningNeg58 q) (meaningNeg62 q) (meaning1665 q) hs
  change (! (valuationOf q 58)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 62 = true ∨ valuation q 1665 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1666 = true := by
  have hs : count1666 q = (countLit q [-55, -57]) + (countLit q [-58, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -62])
  have hm := merge_right (literal (valuationOf q) (1664)) (literal (valuationOf q) (1666)) (countLit q [-55, -57]) (countLit q [-58, -62]) (count1666 q) 1 (meaning1664 q) (meaning1666 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1666 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1667 = true := by
  have hs : count1666 q = (countLit q [-55, -57]) + (countLit q [-58, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -62])
  have hm := merge_right (literal (valuationOf q) (1665)) (literal (valuationOf q) (1667)) (countLit q [-55, -57]) (countLit q [-58, -62]) (count1666 q) 2 (meaning1665 q) (meaning1667 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1667 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1666 = true := by
  have hs : count1666 q = (countLit q [-55, -57]) + (countLit q [-58, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -62])
  have hm := merge_left (literal (valuationOf q) (1662)) (literal (valuationOf q) (1666)) (countLit q [-55, -57]) (countLit q [-58, -62]) (count1666 q) 1 (meaning1662 q) (meaning1666 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1666 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1667 = true := by
  have hs : count1666 q = (countLit q [-55, -57]) + (countLit q [-58, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -62])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1667)) (countLit q [-55, -57]) (countLit q [-58, -62]) (count1666 q) 1 1 (meaning1662 q) (meaning1664 q) (meaning1667 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1664 = false ∨ valuation q 1667 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1668 = true := by
  have hs : count1666 q = (countLit q [-55, -57]) + (countLit q [-58, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -62])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1668)) (countLit q [-55, -57]) (countLit q [-58, -62]) (count1666 q) 1 2 (meaning1662 q) (meaning1665 q) (meaning1668 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1665 = false ∨ valuation q 1668 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1667 = true := by
  have hs : count1666 q = (countLit q [-55, -57]) + (countLit q [-58, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -62])
  have hm := merge_left (literal (valuationOf q) (1663)) (literal (valuationOf q) (1667)) (countLit q [-55, -57]) (countLit q [-58, -62]) (count1666 q) 2 (meaning1663 q) (meaning1667 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1667 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1668 = true := by
  have hs : count1666 q = (countLit q [-55, -57]) + (countLit q [-58, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -57]) (l₂ := [-58, -62])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1668)) (countLit q [-55, -57]) (countLit q [-58, -62]) (count1666 q) 2 1 (meaning1663 q) (meaning1664 q) (meaning1668 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1664 = false ∨ valuation q 1668 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E055.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112055
