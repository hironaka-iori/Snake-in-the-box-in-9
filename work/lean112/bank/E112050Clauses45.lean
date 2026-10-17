import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1743 = true := by
  have hs : count1743 q = (countLit q [-88, -91]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-88, -91]) (l₂ := [-92, -95])
  have hm := merge_left (literal (valuationOf q) (1739)) (literal (valuationOf q) (1743)) (countLit q [-88, -91]) (countLit q [-92, -95]) (count1743 q) 1 (meaning1739 q) (meaning1743 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1743 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1744 = true := by
  have hs : count1743 q = (countLit q [-88, -91]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-88, -91]) (l₂ := [-92, -95])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1741)) (literal (valuationOf q) (1744)) (countLit q [-88, -91]) (countLit q [-92, -95]) (count1743 q) 1 1 (meaning1739 q) (meaning1741 q) (meaning1744 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1741 = false ∨ valuation q 1744 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1745 = true := by
  have hs : count1743 q = (countLit q [-88, -91]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-88, -91]) (l₂ := [-92, -95])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1742)) (literal (valuationOf q) (1745)) (countLit q [-88, -91]) (countLit q [-92, -95]) (count1743 q) 1 2 (meaning1739 q) (meaning1742 q) (meaning1745 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1742 = false ∨ valuation q 1745 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 1740 = false ∨ valuationOf q 1744 = true := by
  have hs : count1743 q = (countLit q [-88, -91]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-88, -91]) (l₂ := [-92, -95])
  have hm := merge_left (literal (valuationOf q) (1740)) (literal (valuationOf q) (1744)) (countLit q [-88, -91]) (countLit q [-92, -95]) (count1743 q) 2 (meaning1740 q) (meaning1744 q) hs
  change valuationOf q 1740 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1740 = false ∨ valuation q 1744 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1740 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1745 = true := by
  have hs : count1743 q = (countLit q [-88, -91]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-88, -91]) (l₂ := [-92, -95])
  have hm := merge_two (literal (valuationOf q) (1740)) (literal (valuationOf q) (1741)) (literal (valuationOf q) (1745)) (countLit q [-88, -91]) (countLit q [-92, -95]) (count1743 q) 2 1 (meaning1740 q) (meaning1741 q) (meaning1745 q) hs
  change valuationOf q 1740 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1740 = false ∨ valuation q 1741 = false ∨ valuation q 1745 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 1740 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1746 = true := by
  have hs : count1743 q = (countLit q [-88, -91]) + (countLit q [-92, -95]) := List.countP_append (p := literal q) (l₁ := [-88, -91]) (l₂ := [-92, -95])
  have hm := merge_two (literal (valuationOf q) (1740)) (literal (valuationOf q) (1742)) (literal (valuationOf q) (1746)) (countLit q [-88, -91]) (countLit q [-92, -95]) (count1743 q) 2 2 (meaning1740 q) (meaning1742 q) (meaning1746 q) hs
  change valuationOf q 1740 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1740 = false ∨ valuation q 1742 = false ∨ valuation q 1746 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 1743 = false ∨ valuationOf q 1747 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_right (literal (valuationOf q) (1743)) (literal (valuationOf q) (1747)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 1 (meaning1743 q) (meaning1747 q) hs
  change valuationOf q 1743 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1743 = false ∨ valuation q 1747 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 1744 = false ∨ valuationOf q 1748 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_right (literal (valuationOf q) (1744)) (literal (valuationOf q) (1748)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 2 (meaning1744 q) (meaning1748 q) hs
  change valuationOf q 1744 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1744 = false ∨ valuation q 1748 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1749 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_right (literal (valuationOf q) (1745)) (literal (valuationOf q) (1749)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 3 (meaning1745 q) (meaning1749 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1749 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1750 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_right (literal (valuationOf q) (1746)) (literal (valuationOf q) (1750)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 4 (meaning1746 q) (meaning1750 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1750 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1747 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_left (literal (valuationOf q) (1735)) (literal (valuationOf q) (1747)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 1 (meaning1735 q) (meaning1747 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1747 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1748 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1748)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 1 1 (meaning1735 q) (meaning1743 q) (meaning1748 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1743 = false ∨ valuation q 1748 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1749 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1744)) (literal (valuationOf q) (1749)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 1 2 (meaning1735 q) (meaning1744 q) (meaning1749 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1744 = false ∨ valuation q 1749 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1750 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1750)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 1 3 (meaning1735 q) (meaning1745 q) (meaning1750 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1745 = false ∨ valuation q 1750 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1751 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1746)) (literal (valuationOf q) (1751)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 1 4 (meaning1735 q) (meaning1746 q) (meaning1751 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1746 = false ∨ valuation q 1751 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1748 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_left (literal (valuationOf q) (1736)) (literal (valuationOf q) (1748)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 2 (meaning1736 q) (meaning1748 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1748 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1749 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1749)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 2 1 (meaning1736 q) (meaning1743 q) (meaning1749 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1743 = false ∨ valuation q 1749 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1750 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1744)) (literal (valuationOf q) (1750)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 2 2 (meaning1736 q) (meaning1744 q) (meaning1750 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1744 = false ∨ valuation q 1750 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1751 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1751)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 2 3 (meaning1736 q) (meaning1745 q) (meaning1751 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1745 = false ∨ valuation q 1751 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1752 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1746)) (literal (valuationOf q) (1752)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 2 4 (meaning1736 q) (meaning1746 q) (meaning1752 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1746 = false ∨ valuation q 1752 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1749 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_left (literal (valuationOf q) (1737)) (literal (valuationOf q) (1749)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 3 (meaning1737 q) (meaning1749 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1749 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1750 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1750)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 3 1 (meaning1737 q) (meaning1743 q) (meaning1750 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1743 = false ∨ valuation q 1750 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1751 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1744)) (literal (valuationOf q) (1751)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 3 2 (meaning1737 q) (meaning1744 q) (meaning1751 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1744 = false ∨ valuation q 1751 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1752 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1752)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 3 3 (meaning1737 q) (meaning1745 q) (meaning1752 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1745 = false ∨ valuation q 1752 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1753 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1746)) (literal (valuationOf q) (1753)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 3 4 (meaning1737 q) (meaning1746 q) (meaning1753 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1746 = false ∨ valuation q 1753 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1750 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_left (literal (valuationOf q) (1738)) (literal (valuationOf q) (1750)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 4 (meaning1738 q) (meaning1750 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1750 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1751 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1751)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 4 1 (meaning1738 q) (meaning1743 q) (meaning1751 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1743 = false ∨ valuation q 1751 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1752 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1744)) (literal (valuationOf q) (1752)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 4 2 (meaning1738 q) (meaning1744 q) (meaning1752 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1744 = false ∨ valuation q 1752 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1753 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1753)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 4 3 (meaning1738 q) (meaning1745 q) (meaning1753 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1745 = false ∨ valuation q 1753 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1754 = true := by
  have hs : count1747 q = (countLit q [-82, -83, -85, -87]) + (countLit q [-88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-82, -83, -85, -87]) (l₂ := [-88, -91, -92, -95])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1746)) (literal (valuationOf q) (1754)) (countLit q [-82, -83, -85, -87]) (countLit q [-88, -91, -92, -95]) (count1747 q) 4 4 (meaning1738 q) (meaning1746 q) (meaning1754 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1746 = false ∨ valuation q 1754 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 1748 = false ∨ valuationOf q 1756 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_right (literal (valuationOf q) (1748)) (literal (valuationOf q) (1756)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 2 (meaning1748 q) (meaning1756 q) hs
  change valuationOf q 1748 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1748 = false ∨ valuation q 1756 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1751 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) + (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69, -72, -73, -78, -79]) (l₂ := [-82, -83, -85, -87, -88, -91, -92, -95])
  have hm := merge_right (literal (valuationOf q) (1751)) (literal (valuationOf q) (1759)) (countLit q [-65, -66, -68, -69, -72, -73, -78, -79]) (countLit q [-82, -83, -85, -87, -88, -91, -92, -95]) (count1755 q) 5 (meaning1751 q) (meaning1759 q) hs
  change valuationOf q 1751 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1751 = false ∨ valuation q 1759 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E050.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112050
