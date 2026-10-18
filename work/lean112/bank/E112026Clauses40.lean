import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1704 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1704)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 3 1 (meaning1671 q) (meaning1693 q) (meaning1704 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1693 = false ∨ valuation q 1704 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1705 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1705)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 3 2 (meaning1671 q) (meaning1694 q) (meaning1705 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1694 = false ∨ valuation q 1705 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1706 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1706)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 3 3 (meaning1671 q) (meaning1695 q) (meaning1706 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1695 = false ∨ valuation q 1706 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1707 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1707)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 3 4 (meaning1671 q) (meaning1696 q) (meaning1707 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1696 = false ∨ valuation q 1707 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1708 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1708)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 3 5 (meaning1671 q) (meaning1697 q) (meaning1708 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1697 = false ∨ valuation q 1708 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1705 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1705)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 4 1 (meaning1672 q) (meaning1693 q) (meaning1705 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1693 = false ∨ valuation q 1705 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1706 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1706)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 4 2 (meaning1672 q) (meaning1694 q) (meaning1706 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1694 = false ∨ valuation q 1706 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1707 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1707)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 4 3 (meaning1672 q) (meaning1695 q) (meaning1707 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1695 = false ∨ valuation q 1707 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1708 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1708)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 4 4 (meaning1672 q) (meaning1696 q) (meaning1708 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1696 = false ∨ valuation q 1708 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1709 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1709)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 4 5 (meaning1672 q) (meaning1697 q) (meaning1709 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1697 = false ∨ valuation q 1709 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1706 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1706)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 5 1 (meaning1673 q) (meaning1693 q) (meaning1706 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1693 = false ∨ valuation q 1706 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1707 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1707)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 5 2 (meaning1673 q) (meaning1694 q) (meaning1707 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1694 = false ∨ valuation q 1707 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1708 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1708)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 5 3 (meaning1673 q) (meaning1695 q) (meaning1708 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1695 = false ∨ valuation q 1708 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1709 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1709)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 5 4 (meaning1673 q) (meaning1696 q) (meaning1709 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1696 = false ∨ valuation q 1709 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1710 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1710)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 5 5 (meaning1673 q) (meaning1697 q) (meaning1710 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1697 = false ∨ valuation q 1710 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1706 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_left (literal (valuationOf q) (1674)) (literal (valuationOf q) (1706)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 6 (meaning1674 q) (meaning1706 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1706 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1707 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1707)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 6 1 (meaning1674 q) (meaning1693 q) (meaning1707 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1693 = false ∨ valuation q 1707 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1708 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1708)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 6 2 (meaning1674 q) (meaning1694 q) (meaning1708 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1694 = false ∨ valuation q 1708 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1709 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1709)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 6 3 (meaning1674 q) (meaning1695 q) (meaning1709 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1695 = false ∨ valuation q 1709 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1710 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1710)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 6 4 (meaning1674 q) (meaning1696 q) (meaning1710 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1696 = false ∨ valuation q 1710 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1708 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1708)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 7 1 (meaning1675 q) (meaning1693 q) (meaning1708 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1693 = false ∨ valuation q 1708 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1709 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1709)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 7 2 (meaning1675 q) (meaning1694 q) (meaning1709 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1694 = false ∨ valuation q 1709 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1710 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1710)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 7 3 (meaning1675 q) (meaning1695 q) (meaning1710 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1695 = false ∨ valuation q 1710 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1709 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1709)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 8 1 (meaning1676 q) (meaning1693 q) (meaning1709 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1693 = false ∨ valuation q 1709 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1724 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1724)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 2 6 (meaning1638 q) (meaning1706 q) (meaning1724 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1706 = false ∨ valuation q 1724 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1725 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1725)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 2 7 (meaning1638 q) (meaning1707 q) (meaning1725 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1707 = false ∨ valuation q 1725 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1726 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1726)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 2 8 (meaning1638 q) (meaning1708 q) (meaning1726 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1708 = false ∨ valuation q 1726 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1727 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1727)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 2 9 (meaning1638 q) (meaning1709 q) (meaning1727 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1709 = false ∨ valuation q 1727 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1728)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 2 10 (meaning1638 q) (meaning1710 q) (meaning1728 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1710 = false ∨ valuation q 1728 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1725 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1725)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 3 6 (meaning1639 q) (meaning1706 q) (meaning1725 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1706 = false ∨ valuation q 1725 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1726 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1726)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 3 7 (meaning1639 q) (meaning1707 q) (meaning1726 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1707 = false ∨ valuation q 1726 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1727 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1727)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 3 8 (meaning1639 q) (meaning1708 q) (meaning1727 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1708 = false ∨ valuation q 1727 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E026.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112026
