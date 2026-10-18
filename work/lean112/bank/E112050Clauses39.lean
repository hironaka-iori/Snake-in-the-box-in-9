import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1652)) (countLit q [-62]) (countLit q [-63]) (count1652 q) 1 (meaningNeg63 q) (meaning1652 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1652 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (1652)) (countLit q [-62]) (countLit q [-63]) (count1652 q) 1 (meaningNeg62 q) (meaning1652 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1652 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1653)) (countLit q [-62]) (countLit q [-63]) (count1652 q) 1 1 (meaningNeg62 q) (meaningNeg63 q) (meaning1653 q) hs
  change (! (valuationOf q 62)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 63 = true ∨ valuation q 1653 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_right (literal (valuationOf q) (1652)) (literal (valuationOf q) (1654)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1654 q) 1 (meaning1652 q) (meaning1654 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1654 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1655 = true := by
  have hs : count1654 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_right (literal (valuationOf q) (1653)) (literal (valuationOf q) (1655)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1654 q) 2 (meaning1653 q) (meaning1655 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1655 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_left (literal (valuationOf q) (1650)) (literal (valuationOf q) (1654)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1654 q) 1 (meaning1650 q) (meaning1654 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1654 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1655 = true := by
  have hs : count1654 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1655)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1654 q) 1 1 (meaning1650 q) (meaning1652 q) (meaning1655 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1652 = false ∨ valuation q 1655 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1656 = true := by
  have hs : count1654 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1656)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1654 q) 1 2 (meaning1650 q) (meaning1653 q) (meaning1656 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1653 = false ∨ valuation q 1656 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1655 = true := by
  have hs : count1654 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_left (literal (valuationOf q) (1651)) (literal (valuationOf q) (1655)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1654 q) 2 (meaning1651 q) (meaning1655 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1655 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1656 = true := by
  have hs : count1654 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1656)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1654 q) 2 1 (meaning1651 q) (meaning1652 q) (meaning1656 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1652 = false ∨ valuation q 1656 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1657 = true := by
  have hs : count1654 q = (countLit q [-56, -60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-56, -60]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1657)) (countLit q [-56, -60]) (countLit q [-62, -63]) (count1654 q) 2 2 (meaning1651 q) (meaning1653 q) (meaning1657 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1653 = false ∨ valuation q 1657 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1658 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_right (literal (valuationOf q) (1654)) (literal (valuationOf q) (1658)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 1 (meaning1654 q) (meaning1658 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1658 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1659 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_right (literal (valuationOf q) (1655)) (literal (valuationOf q) (1659)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 2 (meaning1655 q) (meaning1659 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1659 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1660 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_right (literal (valuationOf q) (1656)) (literal (valuationOf q) (1660)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 3 (meaning1656 q) (meaning1660 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1660 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1661 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_right (literal (valuationOf q) (1657)) (literal (valuationOf q) (1661)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 4 (meaning1657 q) (meaning1661 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1661 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1658 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1646)) (literal (valuationOf q) (1658)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 1 (meaning1646 q) (meaning1658 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1658 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1659 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1659)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 1 1 (meaning1646 q) (meaning1654 q) (meaning1659 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1654 = false ∨ valuation q 1659 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1660 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1660)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 1 2 (meaning1646 q) (meaning1655 q) (meaning1660 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1655 = false ∨ valuation q 1660 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1661 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1661)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 1 3 (meaning1646 q) (meaning1656 q) (meaning1661 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1656 = false ∨ valuation q 1661 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1662 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1662)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 1 4 (meaning1646 q) (meaning1657 q) (meaning1662 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1657 = false ∨ valuation q 1662 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1659 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1647)) (literal (valuationOf q) (1659)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 2 (meaning1647 q) (meaning1659 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1659 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1660 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1660)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 2 1 (meaning1647 q) (meaning1654 q) (meaning1660 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1654 = false ∨ valuation q 1660 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1661 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1661)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 2 2 (meaning1647 q) (meaning1655 q) (meaning1661 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1655 = false ∨ valuation q 1661 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1662 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1662)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 2 3 (meaning1647 q) (meaning1656 q) (meaning1662 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1656 = false ∨ valuation q 1662 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1663 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1663)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 2 4 (meaning1647 q) (meaning1657 q) (meaning1663 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1657 = false ∨ valuation q 1663 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1660 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1648)) (literal (valuationOf q) (1660)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 3 (meaning1648 q) (meaning1660 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1660 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1661 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1661)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 3 1 (meaning1648 q) (meaning1654 q) (meaning1661 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1654 = false ∨ valuation q 1661 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1662 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1662)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 3 2 (meaning1648 q) (meaning1655 q) (meaning1662 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1655 = false ∨ valuation q 1662 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1663 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1663)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 3 3 (meaning1648 q) (meaning1656 q) (meaning1663 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1656 = false ∨ valuation q 1663 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1661 = true := by
  have hs : count1658 q = (countLit q [-46, -51, -53, -54]) + (countLit q [-56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-46, -51, -53, -54]) (l₂ := [-56, -60, -62, -63])
  have hm := merge_left (literal (valuationOf q) (1649)) (literal (valuationOf q) (1661)) (countLit q [-46, -51, -53, -54]) (countLit q [-56, -60, -62, -63]) (count1658 q) 4 (meaning1649 q) (meaning1661 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1661 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1667 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_right (literal (valuationOf q) (1659)) (literal (valuationOf q) (1667)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 2 (meaning1659 q) (meaning1667 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1667 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1668 = true := by
  have hs : count1666 q = (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) + (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36, -39, -42, -43, -45]) (l₂ := [-46, -51, -53, -54, -56, -60, -62, -63])
  have hm := merge_right (literal (valuationOf q) (1660)) (literal (valuationOf q) (1668)) (countLit q [-30, -33, -35, -36, -39, -42, -43, -45]) (countLit q [-46, -51, -53, -54, -56, -60, -62, -63]) (count1666 q) 3 (meaning1660 q) (meaning1668 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1668 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E050.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112050
