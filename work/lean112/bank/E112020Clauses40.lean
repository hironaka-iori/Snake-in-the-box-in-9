import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1654 = true := by
  have hs : count1653 q = (countLit q [-69]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1654)) (countLit q [-69]) (countLit q [-73]) (count1653 q) 1 1 (meaningNeg69 q) (meaningNeg73 q) (meaning1654 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 73 = true ∨ valuation q 1654 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-66, -68]) + (countLit q [-69, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -73])
  have hm := merge_right (literal (valuationOf q) (1653)) (literal (valuationOf q) (1655)) (countLit q [-66, -68]) (countLit q [-69, -73]) (count1655 q) 1 (meaning1653 q) (meaning1655 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1655 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-66, -68]) + (countLit q [-69, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -73])
  have hm := merge_right (literal (valuationOf q) (1654)) (literal (valuationOf q) (1656)) (countLit q [-66, -68]) (countLit q [-69, -73]) (count1655 q) 2 (meaning1654 q) (meaning1656 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1656 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-66, -68]) + (countLit q [-69, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -73])
  have hm := merge_left (literal (valuationOf q) (1651)) (literal (valuationOf q) (1655)) (countLit q [-66, -68]) (countLit q [-69, -73]) (count1655 q) 1 (meaning1651 q) (meaning1655 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1655 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-66, -68]) + (countLit q [-69, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -73])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1656)) (countLit q [-66, -68]) (countLit q [-69, -73]) (count1655 q) 1 1 (meaning1651 q) (meaning1653 q) (meaning1656 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1653 = false ∨ valuation q 1656 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-66, -68]) + (countLit q [-69, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -73])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1657)) (countLit q [-66, -68]) (countLit q [-69, -73]) (count1655 q) 1 2 (meaning1651 q) (meaning1654 q) (meaning1657 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1654 = false ∨ valuation q 1657 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-66, -68]) + (countLit q [-69, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -73])
  have hm := merge_left (literal (valuationOf q) (1652)) (literal (valuationOf q) (1656)) (countLit q [-66, -68]) (countLit q [-69, -73]) (count1655 q) 2 (meaning1652 q) (meaning1656 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1656 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-66, -68]) + (countLit q [-69, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -73])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1657)) (countLit q [-66, -68]) (countLit q [-69, -73]) (count1655 q) 2 1 (meaning1652 q) (meaning1653 q) (meaning1657 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1653 = false ∨ valuation q 1657 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-66, -68]) + (countLit q [-69, -73]) := List.countP_append (p := literal q) (l₁ := [-66, -68]) (l₂ := [-69, -73])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1658)) (countLit q [-66, -68]) (countLit q [-69, -73]) (count1655 q) 2 2 (meaning1652 q) (meaning1654 q) (meaning1658 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1654 = false ∨ valuation q 1658 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_right (literal (valuationOf q) (1655)) (literal (valuationOf q) (1659)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 1 (meaning1655 q) (meaning1659 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1659 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_right (literal (valuationOf q) (1656)) (literal (valuationOf q) (1660)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 2 (meaning1656 q) (meaning1660 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1660 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1661 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_right (literal (valuationOf q) (1657)) (literal (valuationOf q) (1661)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 3 (meaning1657 q) (meaning1661 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1661 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1662 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_right (literal (valuationOf q) (1658)) (literal (valuationOf q) (1662)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 4 (meaning1658 q) (meaning1662 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1662 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_left (literal (valuationOf q) (1647)) (literal (valuationOf q) (1659)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 1 (meaning1647 q) (meaning1659 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1659 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1660)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 1 1 (meaning1647 q) (meaning1655 q) (meaning1660 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1655 = false ∨ valuation q 1660 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1661 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1661)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 1 2 (meaning1647 q) (meaning1656 q) (meaning1661 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1656 = false ∨ valuation q 1661 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1662 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1662)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 1 3 (meaning1647 q) (meaning1657 q) (meaning1662 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1657 = false ∨ valuation q 1662 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1663 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1663)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 1 4 (meaning1647 q) (meaning1658 q) (meaning1663 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1658 = false ∨ valuation q 1663 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_left (literal (valuationOf q) (1648)) (literal (valuationOf q) (1660)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 2 (meaning1648 q) (meaning1660 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1660 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1661 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1661)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 2 1 (meaning1648 q) (meaning1655 q) (meaning1661 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1655 = false ∨ valuation q 1661 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1662 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1662)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 2 2 (meaning1648 q) (meaning1656 q) (meaning1662 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1656 = false ∨ valuation q 1662 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1663 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1663)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 2 3 (meaning1648 q) (meaning1657 q) (meaning1663 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1657 = false ∨ valuation q 1663 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1664 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1664)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 2 4 (meaning1648 q) (meaning1658 q) (meaning1664 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1658 = false ∨ valuation q 1664 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1661 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_left (literal (valuationOf q) (1649)) (literal (valuationOf q) (1661)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 3 (meaning1649 q) (meaning1661 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1661 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1662 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1662)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 3 1 (meaning1649 q) (meaning1655 q) (meaning1662 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1655 = false ∨ valuation q 1662 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1663 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1663)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 3 2 (meaning1649 q) (meaning1656 q) (meaning1663 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1656 = false ∨ valuation q 1663 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1664 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1664)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 3 3 (meaning1649 q) (meaning1657 q) (meaning1664 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1657 = false ∨ valuation q 1664 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1662 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_left (literal (valuationOf q) (1650)) (literal (valuationOf q) (1662)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 4 (meaning1650 q) (meaning1662 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1662 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1663 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1663)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 4 1 (meaning1650 q) (meaning1655 q) (meaning1663 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1655 = false ∨ valuation q 1663 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1664 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1664)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 4 2 (meaning1650 q) (meaning1656 q) (meaning1664 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1656 = false ∨ valuation q 1664 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1665 = true := by
  have hs : count1659 q = (countLit q [-58, -60, -61, -65]) + (countLit q [-66, -68, -69, -73]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65]) (l₂ := [-66, -68, -69, -73])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1665)) (countLit q [-58, -60, -61, -65]) (countLit q [-66, -68, -69, -73]) (count1659 q) 4 3 (meaning1650 q) (meaning1657 q) (meaning1665 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1657 = false ∨ valuation q 1665 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1667 = true := by
  have hs : count1667 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1667)) (countLit q [-75]) (countLit q [-76]) (count1667 q) 1 (meaningNeg76 q) (meaning1667 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1667 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E020.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112020
