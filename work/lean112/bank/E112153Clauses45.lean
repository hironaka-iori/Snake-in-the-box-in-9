import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1615 = true := by
  have hs : count1612 q = (countLit q [-31, -33, -34, -36, -40, -41, -42, -44]) + (countLit q [-48, -49, -50, -54, -56, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -40, -41, -42, -44]) (l₂ := [-48, -49, -50, -54, -56, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1615)) (countLit q [-31, -33, -34, -36, -40, -41, -42, -44]) (countLit q [-48, -49, -50, -54, -56, -58, -59, -62]) (count1612 q) 3 1 (meaning1582 q) (meaning1604 q) (meaning1615 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1604 = false ∨ valuation q 1615 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1638 = true := by
  have hs : count1628 q = (countLit q [-2, -6, -7, -9, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -30]) + (countLit q [-31, -33, -34, -36, -40, -41, -42, -44, -48, -49, -50, -54, -56, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -7, -9, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -30]) (l₂ := [-31, -33, -34, -36, -40, -41, -42, -44, -48, -49, -50, -54, -56, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1555)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1638)) (countLit q [-2, -6, -7, -9, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -30]) (countLit q [-31, -33, -34, -36, -40, -41, -42, -44, -48, -49, -50, -54, -56, -58, -59, -62]) (count1628 q) 7 4 (meaning1555 q) (meaning1615 q) (meaning1638 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1615 = false ∨ valuation q 1638 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (1650)) (countLit q [-66]) (countLit q [-67]) (count1650 q) 1 (meaningNeg67 q) (meaning1650 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1650 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-66]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (1650)) (countLit q [-66]) (countLit q [-67]) (count1650 q) 1 (meaningNeg66 q) (meaning1650 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1650 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-64]) + (countLit q [-66, -67]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66, -67])
  have hm := merge_right (literal (valuationOf q) (1650)) (literal (valuationOf q) (1652)) (countLit q [-64]) (countLit q [-66, -67]) (count1652 q) 1 (meaning1650 q) (meaning1652 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1652 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1655)) (countLit q [-69]) (countLit q [-70]) (count1655 q) 1 (meaningNeg70 q) (meaning1655 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1655 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1655)) (countLit q [-69]) (countLit q [-70]) (count1655 q) 1 (meaningNeg69 q) (meaning1655 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1655 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-72]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1657)) (countLit q [-72]) (countLit q [-76]) (count1657 q) 1 (meaningNeg76 q) (meaning1657 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1657 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-72]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1657)) (countLit q [-72]) (countLit q [-76]) (count1657 q) 1 (meaningNeg72 q) (meaning1657 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1657 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1658 = true := by
  have hs : count1657 q = (countLit q [-72]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1658)) (countLit q [-72]) (countLit q [-76]) (count1657 q) 1 1 (meaningNeg72 q) (meaningNeg76 q) (meaning1658 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 76 = true ∨ valuation q 1658 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-69, -70]) + (countLit q [-72, -76]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-72, -76])
  have hm := merge_right (literal (valuationOf q) (1657)) (literal (valuationOf q) (1659)) (countLit q [-69, -70]) (countLit q [-72, -76]) (count1659 q) 1 (meaning1657 q) (meaning1659 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1659 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-69, -70]) + (countLit q [-72, -76]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-72, -76])
  have hm := merge_right (literal (valuationOf q) (1658)) (literal (valuationOf q) (1660)) (countLit q [-69, -70]) (countLit q [-72, -76]) (count1659 q) 2 (meaning1658 q) (meaning1660 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1660 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-69, -70]) + (countLit q [-72, -76]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-72, -76])
  have hm := merge_left (literal (valuationOf q) (1655)) (literal (valuationOf q) (1659)) (countLit q [-69, -70]) (countLit q [-72, -76]) (count1659 q) 1 (meaning1655 q) (meaning1659 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1659 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-69, -70]) + (countLit q [-72, -76]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-72, -76])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1660)) (countLit q [-69, -70]) (countLit q [-72, -76]) (count1659 q) 1 1 (meaning1655 q) (meaning1657 q) (meaning1660 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1657 = false ∨ valuation q 1660 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1663 = true := by
  have hs : count1663 q = (countLit q [-64, -66, -67]) + (countLit q [-69, -70, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -67]) (l₂ := [-69, -70, -72, -76])
  have hm := merge_right (literal (valuationOf q) (1659)) (literal (valuationOf q) (1663)) (countLit q [-64, -66, -67]) (countLit q [-69, -70, -72, -76]) (count1663 q) 1 (meaning1659 q) (meaning1663 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1663 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1664 = true := by
  have hs : count1663 q = (countLit q [-64, -66, -67]) + (countLit q [-69, -70, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -67]) (l₂ := [-69, -70, -72, -76])
  have hm := merge_right (literal (valuationOf q) (1660)) (literal (valuationOf q) (1664)) (countLit q [-64, -66, -67]) (countLit q [-69, -70, -72, -76]) (count1663 q) 2 (meaning1660 q) (meaning1664 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1664 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1663 = true := by
  have hs : count1663 q = (countLit q [-64, -66, -67]) + (countLit q [-69, -70, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -67]) (l₂ := [-69, -70, -72, -76])
  have hm := merge_left (literal (valuationOf q) (1652)) (literal (valuationOf q) (1663)) (countLit q [-64, -66, -67]) (countLit q [-69, -70, -72, -76]) (count1663 q) 1 (meaning1652 q) (meaning1663 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1663 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1664 = true := by
  have hs : count1663 q = (countLit q [-64, -66, -67]) + (countLit q [-69, -70, -72, -76]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -67]) (l₂ := [-69, -70, -72, -76])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1664)) (countLit q [-64, -66, -67]) (countLit q [-69, -70, -72, -76]) (count1663 q) 1 1 (meaning1652 q) (meaning1659 q) (meaning1664 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1659 = false ∨ valuation q 1664 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1670 = true := by
  have hs : count1670 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1670)) (countLit q [-77]) (countLit q [-78]) (count1670 q) 1 (meaningNeg78 q) (meaning1670 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1670 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1670 = true := by
  have hs : count1670 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1670)) (countLit q [-77]) (countLit q [-78]) (count1670 q) 1 (meaningNeg77 q) (meaning1670 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1670 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1672 = true := by
  have hs : count1672 q = (countLit q [-79]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-83])
  have hm := merge_right (literal (valuationOf q) (-83)) (literal (valuationOf q) (1672)) (countLit q [-79]) (countLit q [-83]) (count1672 q) 1 (meaningNeg83 q) (meaning1672 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1672 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1674 = true := by
  have hs : count1674 q = (countLit q [-77, -78]) + (countLit q [-79, -83]) := List.countP_append (p := literal q) (l₁ := [-77, -78]) (l₂ := [-79, -83])
  have hm := merge_right (literal (valuationOf q) (1672)) (literal (valuationOf q) (1674)) (countLit q [-77, -78]) (countLit q [-79, -83]) (count1674 q) 1 (meaning1672 q) (meaning1674 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1674 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1675 = true := by
  have hs : count1674 q = (countLit q [-77, -78]) + (countLit q [-79, -83]) := List.countP_append (p := literal q) (l₁ := [-77, -78]) (l₂ := [-79, -83])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1675)) (countLit q [-77, -78]) (countLit q [-79, -83]) (count1674 q) 1 1 (meaning1670 q) (meaning1672 q) (meaning1675 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1672 = false ∨ valuation q 1675 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1678 = true := by
  have hs : count1678 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1678)) (countLit q [-84]) (countLit q [-85]) (count1678 q) 1 (meaningNeg85 q) (meaning1678 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1678 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1682 = true := by
  have hs : count1682 q = (countLit q [-84, -85]) + (countLit q [-89, -90]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-89, -90])
  have hm := merge_left (literal (valuationOf q) (1678)) (literal (valuationOf q) (1682)) (countLit q [-84, -85]) (countLit q [-89, -90]) (count1682 q) 1 (meaning1678 q) (meaning1682 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1682 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1687 = true := by
  have hs : count1686 q = (countLit q [-77, -78, -79, -83]) + (countLit q [-84, -85, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -79, -83]) (l₂ := [-84, -85, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1687)) (countLit q [-77, -78, -79, -83]) (countLit q [-84, -85, -89, -90]) (count1686 q) 1 1 (meaning1674 q) (meaning1682 q) (meaning1687 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1682 = false ∨ valuation q 1687 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1688 = true := by
  have hs : count1686 q = (countLit q [-77, -78, -79, -83]) + (countLit q [-84, -85, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -79, -83]) (l₂ := [-84, -85, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1688)) (countLit q [-77, -78, -79, -83]) (countLit q [-84, -85, -89, -90]) (count1686 q) 2 1 (meaning1675 q) (meaning1682 q) (meaning1688 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1682 = false ∨ valuation q 1688 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1697 = true := by
  have hs : count1694 q = (countLit q [-64, -66, -67, -69, -70, -72, -76]) + (countLit q [-77, -78, -79, -83, -84, -85, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -67, -69, -70, -72, -76]) (l₂ := [-77, -78, -79, -83, -84, -85, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1697)) (countLit q [-64, -66, -67, -69, -70, -72, -76]) (countLit q [-77, -78, -79, -83, -84, -85, -89, -90]) (count1694 q) 1 3 (meaning1663 q) (meaning1688 q) (meaning1697 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1688 = false ∨ valuation q 1697 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1697 = true := by
  have hs : count1694 q = (countLit q [-64, -66, -67, -69, -70, -72, -76]) + (countLit q [-77, -78, -79, -83, -84, -85, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -67, -69, -70, -72, -76]) (l₂ := [-77, -78, -79, -83, -84, -85, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1697)) (countLit q [-64, -66, -67, -69, -70, -72, -76]) (countLit q [-77, -78, -79, -83, -84, -85, -89, -90]) (count1694 q) 2 2 (meaning1664 q) (meaning1687 q) (meaning1697 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1687 = false ∨ valuation q 1697 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1709 = true := by
  have hs : count1709 q = (countLit q [-92]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1709)) (countLit q [-92]) (countLit q [-95]) (count1709 q) 1 (meaningNeg92 q) (meaning1709 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1709 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-97]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1711)) (countLit q [-97]) (countLit q [-98]) (count1711 q) 1 (meaningNeg97 q) (meaning1711 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1711 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1714 = true := by
  have hs : count1713 q = (countLit q [-92, -95]) + (countLit q [-97, -98]) := List.countP_append (p := literal q) (l₁ := [-92, -95]) (l₂ := [-97, -98])
  have hm := merge_two (literal (valuationOf q) (1709)) (literal (valuationOf q) (1711)) (literal (valuationOf q) (1714)) (countLit q [-92, -95]) (countLit q [-97, -98]) (count1713 q) 1 1 (meaning1709 q) (meaning1711 q) (meaning1714 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1711 = false ∨ valuation q 1714 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E153.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112153
