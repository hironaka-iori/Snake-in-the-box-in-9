import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1744 = true := by
  have hs : count1743 q = (countLit q [-117, -119]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -119]) (l₂ := [-122, -123])
  have hm := merge_right (literal (valuationOf q) (1742)) (literal (valuationOf q) (1744)) (countLit q [-117, -119]) (countLit q [-122, -123]) (count1743 q) 2 (meaning1742 q) (meaning1744 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1744 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1743 = true := by
  have hs : count1743 q = (countLit q [-117, -119]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -119]) (l₂ := [-122, -123])
  have hm := merge_left (literal (valuationOf q) (1739)) (literal (valuationOf q) (1743)) (countLit q [-117, -119]) (countLit q [-122, -123]) (count1743 q) 1 (meaning1739 q) (meaning1743 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1743 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1744 = true := by
  have hs : count1743 q = (countLit q [-117, -119]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -119]) (l₂ := [-122, -123])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1741)) (literal (valuationOf q) (1744)) (countLit q [-117, -119]) (countLit q [-122, -123]) (count1743 q) 1 1 (meaning1739 q) (meaning1741 q) (meaning1744 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1741 = false ∨ valuation q 1744 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1745 = true := by
  have hs : count1743 q = (countLit q [-117, -119]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -119]) (l₂ := [-122, -123])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1742)) (literal (valuationOf q) (1745)) (countLit q [-117, -119]) (countLit q [-122, -123]) (count1743 q) 1 2 (meaning1739 q) (meaning1742 q) (meaning1745 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1742 = false ∨ valuation q 1745 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1740 = false ∨ valuationOf q 1744 = true := by
  have hs : count1743 q = (countLit q [-117, -119]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -119]) (l₂ := [-122, -123])
  have hm := merge_left (literal (valuationOf q) (1740)) (literal (valuationOf q) (1744)) (countLit q [-117, -119]) (countLit q [-122, -123]) (count1743 q) 2 (meaning1740 q) (meaning1744 q) hs
  change valuationOf q 1740 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1740 = false ∨ valuation q 1744 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1740 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1745 = true := by
  have hs : count1743 q = (countLit q [-117, -119]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -119]) (l₂ := [-122, -123])
  have hm := merge_two (literal (valuationOf q) (1740)) (literal (valuationOf q) (1741)) (literal (valuationOf q) (1745)) (countLit q [-117, -119]) (countLit q [-122, -123]) (count1743 q) 2 1 (meaning1740 q) (meaning1741 q) (meaning1745 q) hs
  change valuationOf q 1740 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1740 = false ∨ valuation q 1741 = false ∨ valuation q 1745 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1740 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1746 = true := by
  have hs : count1743 q = (countLit q [-117, -119]) + (countLit q [-122, -123]) := List.countP_append (p := literal q) (l₁ := [-117, -119]) (l₂ := [-122, -123])
  have hm := merge_two (literal (valuationOf q) (1740)) (literal (valuationOf q) (1742)) (literal (valuationOf q) (1746)) (countLit q [-117, -119]) (countLit q [-122, -123]) (count1743 q) 2 2 (meaning1740 q) (meaning1742 q) (meaning1746 q) hs
  change valuationOf q 1740 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1746 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1740 = false ∨ valuation q 1742 = false ∨ valuation q 1746 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1743 = false ∨ valuationOf q 1747 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1743)) (literal (valuationOf q) (1747)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 1 (meaning1743 q) (meaning1747 q) hs
  change valuationOf q 1743 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1743 = false ∨ valuation q 1747 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1744 = false ∨ valuationOf q 1748 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1744)) (literal (valuationOf q) (1748)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 2 (meaning1744 q) (meaning1748 q) hs
  change valuationOf q 1744 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1744 = false ∨ valuation q 1748 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1749 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1745)) (literal (valuationOf q) (1749)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 3 (meaning1745 q) (meaning1749 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1749 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1750 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1746)) (literal (valuationOf q) (1750)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 4 (meaning1746 q) (meaning1750 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1750 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1747 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1735)) (literal (valuationOf q) (1747)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 1 (meaning1735 q) (meaning1747 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1747 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1748 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1748)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 1 1 (meaning1735 q) (meaning1743 q) (meaning1748 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1743 = false ∨ valuation q 1748 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1749 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1744)) (literal (valuationOf q) (1749)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 1 2 (meaning1735 q) (meaning1744 q) (meaning1749 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1744 = false ∨ valuation q 1749 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1750 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1750)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 1 3 (meaning1735 q) (meaning1745 q) (meaning1750 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1745 = false ∨ valuation q 1750 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1748 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1736)) (literal (valuationOf q) (1748)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 2 (meaning1736 q) (meaning1748 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1748 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1749 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1749)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 2 1 (meaning1736 q) (meaning1743 q) (meaning1749 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1743 = false ∨ valuation q 1749 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1750 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1744)) (literal (valuationOf q) (1750)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 2 2 (meaning1736 q) (meaning1744 q) (meaning1750 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1744 = false ∨ valuation q 1750 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1749 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1737)) (literal (valuationOf q) (1749)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 3 (meaning1737 q) (meaning1749 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1749 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1750 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1750)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 3 1 (meaning1737 q) (meaning1743 q) (meaning1750 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1743 = false ∨ valuation q 1750 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1751 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1744)) (literal (valuationOf q) (1751)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 3 2 (meaning1737 q) (meaning1744 q) (meaning1751 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1744 = false ∨ valuation q 1751 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1750 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1738)) (literal (valuationOf q) (1750)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 4 (meaning1738 q) (meaning1750 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1750 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1751 = true := by
  have hs : count1747 q = (countLit q [-109, -112, -113, -114]) + (countLit q [-117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-109, -112, -113, -114]) (l₂ := [-117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1751)) (countLit q [-109, -112, -113, -114]) (countLit q [-117, -119, -122, -123]) (count1747 q) 4 1 (meaning1738 q) (meaning1743 q) (meaning1751 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1743 = false ∨ valuation q 1751 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1759)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 1 4 (meaning1723 q) (meaning1750 q) (meaning1759 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1750 = false ∨ valuation q 1759 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1757 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1757)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 2 1 (meaning1724 q) (meaning1747 q) (meaning1757 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1747 = false ∨ valuation q 1757 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1758 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1758)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 2 2 (meaning1724 q) (meaning1748 q) (meaning1758 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1748 = false ∨ valuation q 1758 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1759)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 2 3 (meaning1724 q) (meaning1749 q) (meaning1759 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1749 = false ∨ valuation q 1759 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1760)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 2 4 (meaning1724 q) (meaning1750 q) (meaning1760 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1750 = false ∨ valuation q 1760 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1761)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 2 5 (meaning1724 q) (meaning1751 q) (meaning1761 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1751 = false ∨ valuation q 1761 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1759)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 3 2 (meaning1725 q) (meaning1748 q) (meaning1759 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1748 = false ∨ valuation q 1759 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1760)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 3 3 (meaning1725 q) (meaning1749 q) (meaning1760 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1749 = false ∨ valuation q 1760 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) + (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -98, -100, -101, -102, -105, -107]) (l₂ := [-109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1761)) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107]) (countLit q [-109, -112, -113, -114, -117, -119, -122, -123]) (count1755 q) 3 4 (meaning1725 q) (meaning1750 q) (meaning1761 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1750 = false ∨ valuation q 1761 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E186.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112186
