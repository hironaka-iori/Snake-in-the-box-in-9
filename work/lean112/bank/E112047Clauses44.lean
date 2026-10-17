import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1660 = true := by
  have hs : count1656 q = (countLit q [-105, -108, -110]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1660)) (countLit q [-105, -108, -110]) (countLit q [-111, -113, -115, -117]) (count1656 q) 2 3 (meaning1646 q) (meaning1654 q) (meaning1660 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1654 = false ∨ valuation q 1660 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1659 = true := by
  have hs : count1656 q = (countLit q [-105, -108, -110]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1659)) (countLit q [-105, -108, -110]) (countLit q [-111, -113, -115, -117]) (count1656 q) 3 1 (meaning1647 q) (meaning1652 q) (meaning1659 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1652 = false ∨ valuation q 1659 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1660 = true := by
  have hs : count1656 q = (countLit q [-105, -108, -110]) + (countLit q [-111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-105, -108, -110]) (l₂ := [-111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1660)) (countLit q [-105, -108, -110]) (countLit q [-111, -113, -115, -117]) (count1656 q) 3 2 (meaning1647 q) (meaning1653 q) (meaning1660 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1653 = false ∨ valuation q 1660 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1663 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1656)) (literal (valuationOf q) (1663)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 1 (meaning1656 q) (meaning1663 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1663 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1664 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1657)) (literal (valuationOf q) (1664)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 2 (meaning1657 q) (meaning1664 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1664 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1665 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1658)) (literal (valuationOf q) (1665)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 3 (meaning1658 q) (meaning1665 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1665 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1666 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1659)) (literal (valuationOf q) (1666)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 4 (meaning1659 q) (meaning1666 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1666 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1667 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1660)) (literal (valuationOf q) (1667)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 5 (meaning1660 q) (meaning1667 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1667 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1664 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1664)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 1 1 (meaning1636 q) (meaning1656 q) (meaning1664 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1656 = false ∨ valuation q 1664 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1665 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1665)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 1 2 (meaning1636 q) (meaning1657 q) (meaning1665 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1657 = false ∨ valuation q 1665 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1666 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1666)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 1 3 (meaning1636 q) (meaning1658 q) (meaning1666 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1658 = false ∨ valuation q 1666 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1667 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1667)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 1 4 (meaning1636 q) (meaning1659 q) (meaning1667 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1659 = false ∨ valuation q 1667 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1668 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1668)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 1 5 (meaning1636 q) (meaning1660 q) (meaning1668 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1660 = false ∨ valuation q 1668 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1665 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1665)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 2 1 (meaning1637 q) (meaning1656 q) (meaning1665 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1656 = false ∨ valuation q 1665 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1666 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1666)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 2 2 (meaning1637 q) (meaning1657 q) (meaning1666 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1657 = false ∨ valuation q 1666 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1667 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1667)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 2 3 (meaning1637 q) (meaning1658 q) (meaning1667 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1658 = false ∨ valuation q 1667 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1668 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1668)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 2 4 (meaning1637 q) (meaning1659 q) (meaning1668 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1659 = false ∨ valuation q 1668 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1669 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1669)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 2 5 (meaning1637 q) (meaning1660 q) (meaning1669 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1660 = false ∨ valuation q 1669 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1666 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1666)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 3 1 (meaning1638 q) (meaning1656 q) (meaning1666 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1656 = false ∨ valuation q 1666 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1667 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1667)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 3 2 (meaning1638 q) (meaning1657 q) (meaning1667 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1657 = false ∨ valuation q 1667 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1668 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1668)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 3 3 (meaning1638 q) (meaning1658 q) (meaning1668 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1658 = false ∨ valuation q 1668 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1669 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1669)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 3 4 (meaning1638 q) (meaning1659 q) (meaning1669 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1659 = false ∨ valuation q 1669 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1667 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1667)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 4 1 (meaning1639 q) (meaning1656 q) (meaning1667 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1656 = false ∨ valuation q 1667 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1668 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1668)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 4 2 (meaning1639 q) (meaning1657 q) (meaning1668 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1657 = false ∨ valuation q 1668 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1669 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1669)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 4 3 (meaning1639 q) (meaning1658 q) (meaning1669 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1658 = false ∨ valuation q 1669 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1670 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1670)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 4 4 (meaning1639 q) (meaning1659 q) (meaning1670 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1659 = false ∨ valuation q 1670 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1668 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1668)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 5 1 (meaning1640 q) (meaning1656 q) (meaning1668 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1656 = false ∨ valuation q 1668 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1669 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1669)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 5 2 (meaning1640 q) (meaning1657 q) (meaning1669 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1657 = false ∨ valuation q 1669 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1670 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1670)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 5 3 (meaning1640 q) (meaning1658 q) (meaning1670 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1658 = false ∨ valuation q 1670 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1671 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1671)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 5 4 (meaning1640 q) (meaning1659 q) (meaning1671 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1659 = false ∨ valuation q 1671 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1669 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1669)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 6 1 (meaning1641 q) (meaning1656 q) (meaning1669 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1656 = false ∨ valuation q 1669 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1670 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -96, -97, -101, -103, -104]) + (countLit q [-105, -108, -110, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96, -97, -101, -103, -104]) (l₂ := [-105, -108, -110, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1670)) (countLit q [-92, -93, -96, -97, -101, -103, -104]) (countLit q [-105, -108, -110, -111, -113, -115, -117]) (count1663 q) 6 2 (meaning1641 q) (meaning1657 q) (meaning1670 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1657 = false ∨ valuation q 1670 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E047.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112047
