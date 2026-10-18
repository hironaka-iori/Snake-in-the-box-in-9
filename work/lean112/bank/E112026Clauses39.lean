import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 119 = true ∨ valuationOf q 1688 = true := by
  have hs : count1687 q = (countLit q [-118]) + (countLit q [-119]) := List.countP_append (p := literal q) (l₁ := [-118]) (l₂ := [-119])
  have hm := merge_two (literal (valuationOf q) (-118)) (literal (valuationOf q) (-119)) (literal (valuationOf q) (1688)) (countLit q [-118]) (countLit q [-119]) (count1687 q) 1 1 (meaningNeg118 q) (meaningNeg119 q) (meaning1688 q) hs
  change (! (valuationOf q 118)) = false ∨ (! (valuationOf q 119)) = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 119 = true ∨ valuation q 1688 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1687 = false ∨ valuationOf q 1689 = true := by
  have hs : count1689 q = (countLit q [-115, -117]) + (countLit q [-118, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -117]) (l₂ := [-118, -119])
  have hm := merge_right (literal (valuationOf q) (1687)) (literal (valuationOf q) (1689)) (countLit q [-115, -117]) (countLit q [-118, -119]) (count1689 q) 1 (meaning1687 q) (meaning1689 q) hs
  change valuationOf q 1687 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1689 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1690 = true := by
  have hs : count1689 q = (countLit q [-115, -117]) + (countLit q [-118, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -117]) (l₂ := [-118, -119])
  have hm := merge_right (literal (valuationOf q) (1688)) (literal (valuationOf q) (1690)) (countLit q [-115, -117]) (countLit q [-118, -119]) (count1689 q) 2 (meaning1688 q) (meaning1690 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1690 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1685 = false ∨ valuationOf q 1689 = true := by
  have hs : count1689 q = (countLit q [-115, -117]) + (countLit q [-118, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -117]) (l₂ := [-118, -119])
  have hm := merge_left (literal (valuationOf q) (1685)) (literal (valuationOf q) (1689)) (countLit q [-115, -117]) (countLit q [-118, -119]) (count1689 q) 1 (meaning1685 q) (meaning1689 q) hs
  change valuationOf q 1685 = false ∨ valuationOf q 1689 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1685 = false ∨ valuation q 1689 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1685 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1690 = true := by
  have hs : count1689 q = (countLit q [-115, -117]) + (countLit q [-118, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -117]) (l₂ := [-118, -119])
  have hm := merge_two (literal (valuationOf q) (1685)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1690)) (countLit q [-115, -117]) (countLit q [-118, -119]) (count1689 q) 1 1 (meaning1685 q) (meaning1687 q) (meaning1690 q) hs
  change valuationOf q 1685 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1685 = false ∨ valuation q 1687 = false ∨ valuation q 1690 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1685 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1691 = true := by
  have hs : count1689 q = (countLit q [-115, -117]) + (countLit q [-118, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -117]) (l₂ := [-118, -119])
  have hm := merge_two (literal (valuationOf q) (1685)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1691)) (countLit q [-115, -117]) (countLit q [-118, -119]) (count1689 q) 1 2 (meaning1685 q) (meaning1688 q) (meaning1691 q) hs
  change valuationOf q 1685 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1685 = false ∨ valuation q 1688 = false ∨ valuation q 1691 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1686 = false ∨ valuationOf q 1690 = true := by
  have hs : count1689 q = (countLit q [-115, -117]) + (countLit q [-118, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -117]) (l₂ := [-118, -119])
  have hm := merge_left (literal (valuationOf q) (1686)) (literal (valuationOf q) (1690)) (countLit q [-115, -117]) (countLit q [-118, -119]) (count1689 q) 2 (meaning1686 q) (meaning1690 q) hs
  change valuationOf q 1686 = false ∨ valuationOf q 1690 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1686 = false ∨ valuation q 1690 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1686 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1691 = true := by
  have hs : count1689 q = (countLit q [-115, -117]) + (countLit q [-118, -119]) := List.countP_append (p := literal q) (l₁ := [-115, -117]) (l₂ := [-118, -119])
  have hm := merge_two (literal (valuationOf q) (1686)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1691)) (countLit q [-115, -117]) (countLit q [-118, -119]) (count1689 q) 2 1 (meaning1686 q) (meaning1687 q) (meaning1691 q) hs
  change valuationOf q 1686 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1686 = false ∨ valuation q 1687 = false ∨ valuation q 1691 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1693 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_left (literal (valuationOf q) (1681)) (literal (valuationOf q) (1693)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 1 (meaning1681 q) (meaning1693 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1693 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1694 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1694)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 1 1 (meaning1681 q) (meaning1689 q) (meaning1694 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1689 = false ∨ valuation q 1694 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1695 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1695)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 1 2 (meaning1681 q) (meaning1690 q) (meaning1695 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1690 = false ∨ valuation q 1695 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1696 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1696)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 1 3 (meaning1681 q) (meaning1691 q) (meaning1696 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1691 = false ∨ valuation q 1696 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1694 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_left (literal (valuationOf q) (1682)) (literal (valuationOf q) (1694)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 2 (meaning1682 q) (meaning1694 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1694 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1695 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1695)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 2 1 (meaning1682 q) (meaning1689 q) (meaning1695 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1689 = false ∨ valuation q 1695 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1696 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1696)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 2 2 (meaning1682 q) (meaning1690 q) (meaning1696 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1690 = false ∨ valuation q 1696 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1697 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1697)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 2 3 (meaning1682 q) (meaning1691 q) (meaning1697 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1691 = false ∨ valuation q 1697 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1695 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_left (literal (valuationOf q) (1683)) (literal (valuationOf q) (1695)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 3 (meaning1683 q) (meaning1695 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1695 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1696 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1683)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1696)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 3 1 (meaning1683 q) (meaning1689 q) (meaning1696 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1689 = false ∨ valuation q 1696 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1697 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1683)) (literal (valuationOf q) (1690)) (literal (valuationOf q) (1697)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 3 2 (meaning1683 q) (meaning1690 q) (meaning1697 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1690 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1690 = false ∨ valuation q 1697 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1698 = true := by
  have hs : count1693 q = (countLit q [-107, -108, -110, -111]) + (countLit q [-115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -110, -111]) (l₂ := [-115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1683)) (literal (valuationOf q) (1691)) (literal (valuationOf q) (1698)) (countLit q [-107, -108, -110, -111]) (countLit q [-115, -117, -118, -119]) (count1693 q) 3 3 (meaning1683 q) (meaning1691 q) (meaning1698 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1691 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1691 = false ∨ valuation q 1698 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1703 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_right (literal (valuationOf q) (1695)) (literal (valuationOf q) (1703)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 3 (meaning1695 q) (meaning1703 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1703 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1704 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_right (literal (valuationOf q) (1696)) (literal (valuationOf q) (1704)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 4 (meaning1696 q) (meaning1704 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1704 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1705 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_right (literal (valuationOf q) (1697)) (literal (valuationOf q) (1705)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 5 (meaning1697 q) (meaning1705 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1705 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1706 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_right (literal (valuationOf q) (1698)) (literal (valuationOf q) (1706)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 6 (meaning1698 q) (meaning1706 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1706 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1704 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1704)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 1 3 (meaning1669 q) (meaning1695 q) (meaning1704 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1695 = false ∨ valuation q 1704 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1705 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1705)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 1 4 (meaning1669 q) (meaning1696 q) (meaning1705 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1696 = false ∨ valuation q 1705 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1706 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1669)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1706)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 1 5 (meaning1669 q) (meaning1697 q) (meaning1706 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1697 = false ∨ valuation q 1706 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1703 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1703)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 2 1 (meaning1670 q) (meaning1693 q) (meaning1703 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1693 = false ∨ valuation q 1703 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1704 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1704)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 2 2 (meaning1670 q) (meaning1694 q) (meaning1704 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1694 = false ∨ valuation q 1704 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1705 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1705)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 2 3 (meaning1670 q) (meaning1695 q) (meaning1705 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1695 = false ∨ valuation q 1705 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1706 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1706)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 2 4 (meaning1670 q) (meaning1696 q) (meaning1706 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1696 = false ∨ valuation q 1706 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1707 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1707)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 2 5 (meaning1670 q) (meaning1697 q) (meaning1707 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1697 = false ∨ valuation q 1707 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E026.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112026
