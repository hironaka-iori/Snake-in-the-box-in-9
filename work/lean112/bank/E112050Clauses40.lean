import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1669 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_right (literal (valuationOf q) (1661)) (literal (valuationOf q) (1669)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 4 (meaning1661 q) (meaning1669 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1669 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1670 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_right (literal (valuationOf q) (1662)) (literal (valuationOf q) (1670)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 5 (meaning1662 q) (meaning1670 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1670 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1666 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1634)) (literal (valuationOf q) (1666)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 1 (meaning1634 q) (meaning1666 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1666 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1667 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1667)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 1 1 (meaning1634 q) (meaning1658 q) (meaning1667 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1658 = false ∨ valuation q 1667 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1668 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1668)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 1 2 (meaning1634 q) (meaning1659 q) (meaning1668 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1659 = false ∨ valuation q 1668 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1669 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1669)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 1 3 (meaning1634 q) (meaning1660 q) (meaning1669 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1660 = false ∨ valuation q 1669 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1670 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1670)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 1 4 (meaning1634 q) (meaning1661 q) (meaning1670 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1661 = false ∨ valuation q 1670 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1671 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1671)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 1 5 (meaning1634 q) (meaning1662 q) (meaning1671 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1662 = false ∨ valuation q 1671 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1667 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1635)) (literal (valuationOf q) (1667)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 2 (meaning1635 q) (meaning1667 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1667 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1668 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1668)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 2 1 (meaning1635 q) (meaning1658 q) (meaning1668 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1658 = false ∨ valuation q 1668 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1669 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1669)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 2 2 (meaning1635 q) (meaning1659 q) (meaning1669 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1659 = false ∨ valuation q 1669 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1670 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1670)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 2 3 (meaning1635 q) (meaning1660 q) (meaning1670 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1660 = false ∨ valuation q 1670 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1671 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1671)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 2 4 (meaning1635 q) (meaning1661 q) (meaning1671 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1661 = false ∨ valuation q 1671 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1672 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1672)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 2 5 (meaning1635 q) (meaning1662 q) (meaning1672 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1662 = false ∨ valuation q 1672 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1673 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1673)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 2 6 (meaning1635 q) (meaning1663 q) (meaning1673 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1663 = false ∨ valuation q 1673 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1668 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1636)) (literal (valuationOf q) (1668)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 3 (meaning1636 q) (meaning1668 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1668 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1669 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1669)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 3 1 (meaning1636 q) (meaning1658 q) (meaning1669 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1658 = false ∨ valuation q 1669 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1670 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1670)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 3 2 (meaning1636 q) (meaning1659 q) (meaning1670 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1659 = false ∨ valuation q 1670 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1671 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1671)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 3 3 (meaning1636 q) (meaning1660 q) (meaning1671 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1660 = false ∨ valuation q 1671 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1672 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1672)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 3 4 (meaning1636 q) (meaning1661 q) (meaning1672 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1661 = false ∨ valuation q 1672 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1673 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1673)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 3 5 (meaning1636 q) (meaning1662 q) (meaning1673 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1662 = false ∨ valuation q 1673 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1674 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1674)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 3 6 (meaning1636 q) (meaning1663 q) (meaning1674 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1663 = false ∨ valuation q 1674 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1669 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1637)) (literal (valuationOf q) (1669)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 4 (meaning1637 q) (meaning1669 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1669 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1670 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1670)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 4 1 (meaning1637 q) (meaning1658 q) (meaning1670 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1658 = false ∨ valuation q 1670 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1671 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1671)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 4 2 (meaning1637 q) (meaning1659 q) (meaning1671 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1659 = false ∨ valuation q 1671 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1672 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1672)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 4 3 (meaning1637 q) (meaning1660 q) (meaning1672 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1660 = false ∨ valuation q 1672 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1673 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1673)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 4 4 (meaning1637 q) (meaning1661 q) (meaning1673 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1661 = false ∨ valuation q 1673 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1674 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1674)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 4 5 (meaning1637 q) (meaning1662 q) (meaning1674 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1662 = false ∨ valuation q 1674 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1670 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1638)) (literal (valuationOf q) (1670)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 5 (meaning1638 q) (meaning1670 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1670 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1671 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1671)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 5 1 (meaning1638 q) (meaning1658 q) (meaning1671 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1658 = false ∨ valuation q 1671 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1672 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1672)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 5 2 (meaning1638 q) (meaning1659 q) (meaning1672 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1659 = false ∨ valuation q 1672 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1673 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1673)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 5 3 (meaning1638 q) (meaning1660 q) (meaning1673 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1660 = false ∨ valuation q 1673 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E050.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112050
