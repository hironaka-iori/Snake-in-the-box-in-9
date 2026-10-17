import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-68, -71]) + (countLit q [-73, -75]) := List.countP_append (p := literal q) (l₁ := [-68, -71]) (l₂ := [-73, -75])
  have hm := merge_right (literal (valuationOf q) (1639)) (literal (valuationOf q) (1641)) (countLit q [-68, -71]) (countLit q [-73, -75]) (count1641 q) 1 (meaning1639 q) (meaning1641 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-68, -71]) + (countLit q [-73, -75]) := List.countP_append (p := literal q) (l₁ := [-68, -71]) (l₂ := [-73, -75])
  have hm := merge_left (literal (valuationOf q) (1637)) (literal (valuationOf q) (1641)) (countLit q [-68, -71]) (countLit q [-73, -75]) (count1641 q) 1 (meaning1637 q) (meaning1641 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1641 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-63, -66, -67]) + (countLit q [-68, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -67]) (l₂ := [-68, -71, -73, -75])
  have hm := merge_right (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-63, -66, -67]) (countLit q [-68, -71, -73, -75]) (count1645 q) 1 (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1645 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-63, -66, -67]) + (countLit q [-68, -71, -73, -75]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -67]) (l₂ := [-68, -71, -73, -75])
  have hm := merge_left (literal (valuationOf q) (1634)) (literal (valuationOf q) (1645)) (countLit q [-63, -66, -67]) (countLit q [-68, -71, -73, -75]) (count1645 q) 1 (meaning1634 q) (meaning1645 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1645 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1652)) (countLit q [-77]) (countLit q [-78]) (count1652 q) 1 (meaningNeg78 q) (meaning1652 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1652 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1656 = true := by
  have hs : count1656 q = (countLit q [-77, -78]) + (countLit q [-80, -83]) := List.countP_append (p := literal q) (l₁ := [-77, -78]) (l₂ := [-80, -83])
  have hm := merge_left (literal (valuationOf q) (1652)) (literal (valuationOf q) (1656)) (countLit q [-77, -78]) (countLit q [-80, -83]) (count1656 q) 1 (meaning1652 q) (meaning1656 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1656 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1660 = true := by
  have hs : count1660 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1660)) (countLit q [-84]) (countLit q [-85]) (count1660 q) 1 (meaningNeg85 q) (meaning1660 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1660 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1662 = true := by
  have hs : count1662 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1662)) (countLit q [-88]) (countLit q [-90]) (count1662 q) 1 (meaningNeg88 q) (meaning1662 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1662 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1664 = true := by
  have hs : count1664 q = (countLit q [-84, -85]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-88, -90])
  have hm := merge_right (literal (valuationOf q) (1662)) (literal (valuationOf q) (1664)) (countLit q [-84, -85]) (countLit q [-88, -90]) (count1664 q) 1 (meaning1662 q) (meaning1664 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1664 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1665 = true := by
  have hs : count1664 q = (countLit q [-84, -85]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-88, -90])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1665)) (countLit q [-84, -85]) (countLit q [-88, -90]) (count1664 q) 1 1 (meaning1660 q) (meaning1662 q) (meaning1665 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1662 = false ∨ valuation q 1665 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1669 = true := by
  have hs : count1668 q = (countLit q [-77, -78, -80, -83]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -80, -83]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1669)) (countLit q [-77, -78, -80, -83]) (countLit q [-84, -85, -88, -90]) (count1668 q) 1 1 (meaning1656 q) (meaning1664 q) (meaning1669 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1664 = false ∨ valuation q 1669 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1670 = true := by
  have hs : count1668 q = (countLit q [-77, -78, -80, -83]) + (countLit q [-84, -85, -88, -90]) := List.countP_append (p := literal q) (l₁ := [-77, -78, -80, -83]) (l₂ := [-84, -85, -88, -90])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1670)) (countLit q [-77, -78, -80, -83]) (countLit q [-84, -85, -88, -90]) (count1668 q) 1 2 (meaning1656 q) (meaning1665 q) (meaning1670 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1665 = false ∨ valuation q 1670 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1678 = true := by
  have hs : count1676 q = (countLit q [-63, -66, -67, -68, -71, -73, -75]) + (countLit q [-77, -78, -80, -83, -84, -85, -88, -90]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -67, -68, -71, -73, -75]) (l₂ := [-77, -78, -80, -83, -84, -85, -88, -90])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1678)) (countLit q [-63, -66, -67, -68, -71, -73, -75]) (countLit q [-77, -78, -80, -83, -84, -85, -88, -90]) (count1676 q) 1 2 (meaning1645 q) (meaning1669 q) (meaning1678 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1669 = false ∨ valuation q 1678 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1679 = true := by
  have hs : count1676 q = (countLit q [-63, -66, -67, -68, -71, -73, -75]) + (countLit q [-77, -78, -80, -83, -84, -85, -88, -90]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -67, -68, -71, -73, -75]) (l₂ := [-77, -78, -80, -83, -84, -85, -88, -90])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1679)) (countLit q [-63, -66, -67, -68, -71, -73, -75]) (countLit q [-77, -78, -80, -83, -84, -85, -88, -90]) (count1676 q) 1 3 (meaning1645 q) (meaning1670 q) (meaning1679 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1670 = false ∨ valuation q 1679 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1691 = true := by
  have hs : count1691 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1691)) (countLit q [-92]) (countLit q [-93]) (count1691 q) 1 (meaningNeg92 q) (meaning1691 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1691 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1693 = true := by
  have hs : count1693 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1693)) (countLit q [-96]) (countLit q [-98]) (count1693 q) 1 (meaningNeg98 q) (meaning1693 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1693 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 1691 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1696 = true := by
  have hs : count1695 q = (countLit q [-92, -93]) + (countLit q [-96, -98]) := List.countP_append (p := literal q) (l₁ := [-92, -93]) (l₂ := [-96, -98])
  have hm := merge_two (literal (valuationOf q) (1691)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1696)) (countLit q [-92, -93]) (countLit q [-96, -98]) (count1695 q) 1 1 (meaning1691 q) (meaning1693 q) (meaning1696 q) hs
  change valuationOf q 1691 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 1691 = false ∨ valuation q 1693 = false ∨ valuation q 1696 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1699 = true := by
  have hs : count1699 q = (countLit q [-99]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1699)) (countLit q [-99]) (countLit q [-102]) (count1699 q) 1 (meaningNeg102 q) (meaning1699 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1699 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1701 = true := by
  have hs : count1701 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1701)) (countLit q [-103]) (countLit q [-104]) (count1701 q) 1 (meaningNeg104 q) (meaning1701 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1701 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1703 = true := by
  have hs : count1703 q = (countLit q [-99, -102]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -102]) (l₂ := [-103, -104])
  have hm := merge_left (literal (valuationOf q) (1699)) (literal (valuationOf q) (1703)) (countLit q [-99, -102]) (countLit q [-103, -104]) (count1703 q) 1 (meaning1699 q) (meaning1703 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1703 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1704 = true := by
  have hs : count1703 q = (countLit q [-99, -102]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-99, -102]) (l₂ := [-103, -104])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1701)) (literal (valuationOf q) (1704)) (countLit q [-99, -102]) (countLit q [-103, -104]) (count1703 q) 1 1 (meaning1699 q) (meaning1701 q) (meaning1704 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1701 = false ∨ valuation q 1704 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1709 = true := by
  have hs : count1707 q = (countLit q [-92, -93, -96, -98]) + (countLit q [-99, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -98]) (l₂ := [-99, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1709)) (countLit q [-92, -93, -96, -98]) (countLit q [-99, -102, -103, -104]) (count1707 q) 2 1 (meaning1696 q) (meaning1703 q) (meaning1709 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1703 = false ∨ valuation q 1709 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1710 = true := by
  have hs : count1707 q = (countLit q [-92, -93, -96, -98]) + (countLit q [-99, -102, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -98]) (l₂ := [-99, -102, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1710)) (countLit q [-92, -93, -96, -98]) (countLit q [-99, -102, -103, -104]) (count1707 q) 2 2 (meaning1696 q) (meaning1704 q) (meaning1710 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1704 = false ∨ valuation q 1710 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 116 = true ∨ valuationOf q 1718 = true := by
  have hs : count1717 q = (countLit q [-112]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-116])
  have hm := merge_two (literal (valuationOf q) (-112)) (literal (valuationOf q) (-116)) (literal (valuationOf q) (1718)) (countLit q [-112]) (countLit q [-116]) (count1717 q) 1 1 (meaningNeg112 q) (meaningNeg116 q) (meaning1718 q) hs
  change (! (valuationOf q 112)) = false ∨ (! (valuationOf q 116)) = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 116 = true ∨ valuation q 1718 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-107, -110]) + (countLit q [-112, -116]) := List.countP_append (p := literal q) (l₁ := [-107, -110]) (l₂ := [-112, -116])
  have hm := merge_right (literal (valuationOf q) (1718)) (literal (valuationOf q) (1720)) (countLit q [-107, -110]) (countLit q [-112, -116]) (count1719 q) 2 (meaning1718 q) (meaning1720 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1720 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 1723 = true := by
  have hs : count1723 q = (countLit q [-117]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-119])
  have hm := merge_right (literal (valuationOf q) (-119)) (literal (valuationOf q) (1723)) (countLit q [-117]) (countLit q [-119]) (count1723 q) 1 (meaningNeg119 q) (meaning1723 q) hs
  change (! (valuationOf q 119)) = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 1723 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 117 = true ∨ valuationOf q 119 = true ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-117]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-119])
  have hm := merge_two (literal (valuationOf q) (-117)) (literal (valuationOf q) (-119)) (literal (valuationOf q) (1724)) (countLit q [-117]) (countLit q [-119]) (count1723 q) 1 1 (meaningNeg117 q) (meaningNeg119 q) (meaning1724 q) hs
  change (! (valuationOf q 117)) = false ∨ (! (valuationOf q 119)) = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 117 = true ∨ valuation q 119 = true ∨ valuation q 1724 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 123 = true ∨ valuationOf q 1725 = true := by
  have hs : count1725 q = (countLit q [-120]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-120]) (l₂ := [-123])
  have hm := merge_right (literal (valuationOf q) (-123)) (literal (valuationOf q) (1725)) (countLit q [-120]) (countLit q [-123]) (count1725 q) 1 (meaningNeg123 q) (meaning1725 q) hs
  change (! (valuationOf q 123)) = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 123 = true ∨ valuation q 1725 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1728 = true := by
  have hs : count1727 q = (countLit q [-117, -119]) + (countLit q [-120, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -119]) (l₂ := [-120, -123])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1728)) (countLit q [-117, -119]) (countLit q [-120, -123]) (count1727 q) 1 1 (meaning1723 q) (meaning1725 q) (meaning1728 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1725 = false ∨ valuation q 1728 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1729 = true := by
  have hs : count1727 q = (countLit q [-117, -119]) + (countLit q [-120, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -119]) (l₂ := [-120, -123])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1729)) (countLit q [-117, -119]) (countLit q [-120, -123]) (count1727 q) 2 1 (meaning1724 q) (meaning1725 q) (meaning1729 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1725 = false ∨ valuation q 1729 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 1720 = false ∨ valuationOf q 1728 = false ∨ valuationOf q 1734 = true := by
  have hs : count1731 q = (countLit q [-107, -110, -112, -116]) + (countLit q [-117, -119, -120, -123]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -116]) (l₂ := [-117, -119, -120, -123])
  have hm := merge_two (literal (valuationOf q) (1720)) (literal (valuationOf q) (1728)) (literal (valuationOf q) (1734)) (countLit q [-107, -110, -112, -116]) (countLit q [-117, -119, -120, -123]) (count1731 q) 2 2 (meaning1720 q) (meaning1728 q) (meaning1734 q) hs
  change valuationOf q 1720 = false ∨ valuationOf q 1728 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 1720 = false ∨ valuation q 1728 = false ∨ valuation q 1734 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 1720 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1735 = true := by
  have hs : count1731 q = (countLit q [-107, -110, -112, -116]) + (countLit q [-117, -119, -120, -123]) := List.countP_append (p := literal q) (l₁ := [-107, -110, -112, -116]) (l₂ := [-117, -119, -120, -123])
  have hm := merge_two (literal (valuationOf q) (1720)) (literal (valuationOf q) (1729)) (literal (valuationOf q) (1735)) (countLit q [-107, -110, -112, -116]) (countLit q [-117, -119, -120, -123]) (count1731 q) 2 3 (meaning1720 q) (meaning1729 q) (meaning1735 q) hs
  change valuationOf q 1720 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 1720 = false ∨ valuation q 1729 = false ∨ valuation q 1735 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E097.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112097
