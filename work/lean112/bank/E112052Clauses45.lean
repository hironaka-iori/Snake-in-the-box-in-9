import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1660)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 1 5 (meaning1623 q) (meaning1651 q) (meaning1660 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1651 = false ∨ valuation q 1660 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1661 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1661)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 1 6 (meaning1623 q) (meaning1652 q) (meaning1661 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1652 = false ∨ valuation q 1661 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1624)) (literal (valuationOf q) (1656)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 2 (meaning1624 q) (meaning1656 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1656 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1657)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 2 1 (meaning1624 q) (meaning1647 q) (meaning1657 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1647 = false ∨ valuation q 1657 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1658)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 2 2 (meaning1624 q) (meaning1648 q) (meaning1658 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1648 = false ∨ valuation q 1658 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1659)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 2 3 (meaning1624 q) (meaning1649 q) (meaning1659 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1649 = false ∨ valuation q 1659 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1660)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 2 4 (meaning1624 q) (meaning1650 q) (meaning1660 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1650 = false ∨ valuation q 1660 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1661 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1661)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 2 5 (meaning1624 q) (meaning1651 q) (meaning1661 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1651 = false ∨ valuation q 1661 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1662 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1662)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 2 6 (meaning1624 q) (meaning1652 q) (meaning1662 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1652 = false ∨ valuation q 1662 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1625)) (literal (valuationOf q) (1657)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 3 (meaning1625 q) (meaning1657 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1657 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1658)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 3 1 (meaning1625 q) (meaning1647 q) (meaning1658 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1647 = false ∨ valuation q 1658 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1659)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 3 2 (meaning1625 q) (meaning1648 q) (meaning1659 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1648 = false ∨ valuation q 1659 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1660)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 3 3 (meaning1625 q) (meaning1649 q) (meaning1660 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1649 = false ∨ valuation q 1660 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1661 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1661)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 3 4 (meaning1625 q) (meaning1650 q) (meaning1661 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1650 = false ∨ valuation q 1661 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1662 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1662)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 3 5 (meaning1625 q) (meaning1651 q) (meaning1662 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1651 = false ∨ valuation q 1662 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1626)) (literal (valuationOf q) (1658)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 4 (meaning1626 q) (meaning1658 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1658 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1659)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 4 1 (meaning1626 q) (meaning1647 q) (meaning1659 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1647 = false ∨ valuation q 1659 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1660)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 4 2 (meaning1626 q) (meaning1648 q) (meaning1660 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1648 = false ∨ valuation q 1660 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1661 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1661)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 4 3 (meaning1626 q) (meaning1649 q) (meaning1661 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1649 = false ∨ valuation q 1661 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1662 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1662)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 4 4 (meaning1626 q) (meaning1650 q) (meaning1662 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1650 = false ∨ valuation q 1662 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1627)) (literal (valuationOf q) (1659)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 5 (meaning1627 q) (meaning1659 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1659 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1660)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 5 1 (meaning1627 q) (meaning1647 q) (meaning1660 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1647 = false ∨ valuation q 1660 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1661 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1661)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 5 2 (meaning1627 q) (meaning1648 q) (meaning1661 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1648 = false ∨ valuation q 1661 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1662 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1662)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 5 3 (meaning1627 q) (meaning1649 q) (meaning1662 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1649 = false ∨ valuation q 1662 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1663 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1663)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 5 4 (meaning1627 q) (meaning1650 q) (meaning1663 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1650 = false ∨ valuation q 1663 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1628)) (literal (valuationOf q) (1660)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 6 (meaning1628 q) (meaning1660 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1660 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1661 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1661)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 6 1 (meaning1628 q) (meaning1647 q) (meaning1661 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1647 = false ∨ valuation q 1661 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1662 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1662)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 6 2 (meaning1628 q) (meaning1648 q) (meaning1662 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1648 = false ∨ valuation q 1662 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1663 = true := by
  have hs : count1655 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1663)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1655 q) 6 3 (meaning1628 q) (meaning1649 q) (meaning1663 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1649 = false ∨ valuation q 1663 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1678 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1678)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 3 5 (meaning1593 q) (meaning1659 q) (meaning1678 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1659 = false ∨ valuation q 1678 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1680)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 3 7 (meaning1593 q) (meaning1661 q) (meaning1680 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1661 = false ∨ valuation q 1680 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1675 = true := by
  have hs : count1671 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) + (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (l₂ := [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1675)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28]) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (count1671 q) 4 1 (meaning1594 q) (meaning1655 q) (meaning1675 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1655 = false ∨ valuation q 1675 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E052.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112052
