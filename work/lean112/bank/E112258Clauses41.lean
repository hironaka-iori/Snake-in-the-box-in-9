import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1701 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1688)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1701)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 1 2 (meaning1688 q) (meaning1696 q) (meaning1701 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1696 = false ∨ valuation q 1701 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1702 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1688)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1702)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 1 3 (meaning1688 q) (meaning1697 q) (meaning1702 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1697 = false ∨ valuation q 1702 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1688 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1703 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1688)) (literal (valuationOf q) (1698)) (literal (valuationOf q) (1703)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 1 4 (meaning1688 q) (meaning1698 q) (meaning1703 q) hs
  change valuationOf q 1688 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1688 = false ∨ valuation q 1698 = false ∨ valuation q 1703 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1700 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_left (literal (valuationOf q) (1689)) (literal (valuationOf q) (1700)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 2 (meaning1689 q) (meaning1700 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1700 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1701 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1689)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1701)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 2 1 (meaning1689 q) (meaning1695 q) (meaning1701 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1695 = false ∨ valuation q 1701 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1702 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1689)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1702)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 2 2 (meaning1689 q) (meaning1696 q) (meaning1702 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1696 = false ∨ valuation q 1702 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1703 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1689)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1703)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 2 3 (meaning1689 q) (meaning1697 q) (meaning1703 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1697 = false ∨ valuation q 1703 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1689 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1704 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1689)) (literal (valuationOf q) (1698)) (literal (valuationOf q) (1704)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 2 4 (meaning1689 q) (meaning1698 q) (meaning1704 q) hs
  change valuationOf q 1689 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1689 = false ∨ valuation q 1698 = false ∨ valuation q 1704 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1701 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_left (literal (valuationOf q) (1690)) (literal (valuationOf q) (1701)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 3 (meaning1690 q) (meaning1701 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1701 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1701 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1702 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1690)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1702)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 3 1 (meaning1690 q) (meaning1695 q) (meaning1702 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1702 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1695 = false ∨ valuation q 1702 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1703 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1690)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1703)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 3 2 (meaning1690 q) (meaning1696 q) (meaning1703 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1703 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1696 = false ∨ valuation q 1703 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1690 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1704 = true := by
  have hs : count1699 q = (countLit q [-90, -93, -94]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1690)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1704)) (countLit q [-90, -93, -94]) (countLit q [-98, -99, -102, -105]) (count1699 q) 3 3 (meaning1690 q) (meaning1697 q) (meaning1704 q) hs
  change valuationOf q 1690 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1704 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1690 = false ∨ valuation q 1697 = false ∨ valuation q 1704 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1706 = true := by
  have hs : count1706 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1706)) (countLit q [-107]) (countLit q [-108]) (count1706 q) 1 (meaningNeg107 q) (meaning1706 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1706 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1707 = true := by
  have hs : count1706 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-107)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1707)) (countLit q [-107]) (countLit q [-108]) (count1706 q) 1 1 (meaningNeg107 q) (meaningNeg108 q) (meaning1707 q) hs
  change (! (valuationOf q 107)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 108 = true ∨ valuation q 1707 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1708 = true := by
  have hs : count1708 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_right (literal (valuationOf q) (-112)) (literal (valuationOf q) (1708)) (countLit q [-111]) (countLit q [-112]) (count1708 q) 1 (meaningNeg112 q) (meaning1708 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1708 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1708 = true := by
  have hs : count1708 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1708)) (countLit q [-111]) (countLit q [-112]) (count1708 q) 1 (meaningNeg111 q) (meaning1708 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1708 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 112 = true ∨ valuationOf q 1709 = true := by
  have hs : count1708 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-112)) (literal (valuationOf q) (1709)) (countLit q [-111]) (countLit q [-112]) (count1708 q) 1 1 (meaningNeg111 q) (meaningNeg112 q) (meaning1709 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 112)) = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 1709 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1710 = true := by
  have hs : count1710 q = (countLit q [-107, -108]) + (countLit q [-111, -112]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-111, -112])
  have hm := merge_left (literal (valuationOf q) (1706)) (literal (valuationOf q) (1710)) (countLit q [-107, -108]) (countLit q [-111, -112]) (count1710 q) 1 (meaning1706 q) (meaning1710 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1710 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1711 = true := by
  have hs : count1710 q = (countLit q [-107, -108]) + (countLit q [-111, -112]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-111, -112])
  have hm := merge_two (literal (valuationOf q) (1706)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1711)) (countLit q [-107, -108]) (countLit q [-111, -112]) (count1710 q) 1 1 (meaning1706 q) (meaning1708 q) (meaning1711 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1708 = false ∨ valuation q 1711 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1712 = true := by
  have hs : count1710 q = (countLit q [-107, -108]) + (countLit q [-111, -112]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-111, -112])
  have hm := merge_two (literal (valuationOf q) (1706)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1712)) (countLit q [-107, -108]) (countLit q [-111, -112]) (count1710 q) 1 2 (meaning1706 q) (meaning1709 q) (meaning1712 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1709 = false ∨ valuation q 1712 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1711 = true := by
  have hs : count1710 q = (countLit q [-107, -108]) + (countLit q [-111, -112]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-111, -112])
  have hm := merge_left (literal (valuationOf q) (1707)) (literal (valuationOf q) (1711)) (countLit q [-107, -108]) (countLit q [-111, -112]) (count1710 q) 2 (meaning1707 q) (meaning1711 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1711 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1712 = true := by
  have hs : count1710 q = (countLit q [-107, -108]) + (countLit q [-111, -112]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-111, -112])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1712)) (countLit q [-107, -108]) (countLit q [-111, -112]) (count1710 q) 2 1 (meaning1707 q) (meaning1708 q) (meaning1712 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1708 = false ∨ valuation q 1712 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1713 = true := by
  have hs : count1710 q = (countLit q [-107, -108]) + (countLit q [-111, -112]) := List.countP_append (p := literal q) (l₁ := [-107, -108]) (l₂ := [-111, -112])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1713)) (countLit q [-107, -108]) (countLit q [-111, -112]) (count1710 q) 2 2 (meaning1707 q) (meaning1709 q) (meaning1713 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1709 = false ∨ valuation q 1713 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1714 = true := by
  have hs : count1714 q = (countLit q [-113]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-116])
  have hm := merge_right (literal (valuationOf q) (-116)) (literal (valuationOf q) (1714)) (countLit q [-113]) (countLit q [-116]) (count1714 q) 1 (meaningNeg116 q) (meaning1714 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1714 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1714 = true := by
  have hs : count1714 q = (countLit q [-113]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-116])
  have hm := merge_left (literal (valuationOf q) (-113)) (literal (valuationOf q) (1714)) (countLit q [-113]) (countLit q [-116]) (count1714 q) 1 (meaningNeg113 q) (meaning1714 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1714 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 116 = true ∨ valuationOf q 1715 = true := by
  have hs : count1714 q = (countLit q [-113]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-116])
  have hm := merge_two (literal (valuationOf q) (-113)) (literal (valuationOf q) (-116)) (literal (valuationOf q) (1715)) (countLit q [-113]) (countLit q [-116]) (count1714 q) 1 1 (meaningNeg113 q) (meaningNeg116 q) (meaning1715 q) hs
  change (! (valuationOf q 113)) = false ∨ (! (valuationOf q 116)) = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 116 = true ∨ valuation q 1715 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 1716 = true := by
  have hs : count1716 q = (countLit q [-119]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-119]) (l₂ := [-120])
  have hm := merge_right (literal (valuationOf q) (-120)) (literal (valuationOf q) (1716)) (countLit q [-119]) (countLit q [-120]) (count1716 q) 1 (meaningNeg120 q) (meaning1716 q) hs
  change (! (valuationOf q 120)) = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 1716 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 1716 = true := by
  have hs : count1716 q = (countLit q [-119]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-119]) (l₂ := [-120])
  have hm := merge_left (literal (valuationOf q) (-119)) (literal (valuationOf q) (1716)) (countLit q [-119]) (countLit q [-120]) (count1716 q) 1 (meaningNeg119 q) (meaning1716 q) hs
  change (! (valuationOf q 119)) = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 1716 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 120 = true ∨ valuationOf q 1717 = true := by
  have hs : count1716 q = (countLit q [-119]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-119]) (l₂ := [-120])
  have hm := merge_two (literal (valuationOf q) (-119)) (literal (valuationOf q) (-120)) (literal (valuationOf q) (1717)) (countLit q [-119]) (countLit q [-120]) (count1716 q) 1 1 (meaningNeg119 q) (meaningNeg120 q) (meaning1717 q) hs
  change (! (valuationOf q 119)) = false ∨ (! (valuationOf q 120)) = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 1717 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1718 = true := by
  have hs : count1718 q = (countLit q [-113, -116]) + (countLit q [-119, -120]) := List.countP_append (p := literal q) (l₁ := [-113, -116]) (l₂ := [-119, -120])
  have hm := merge_right (literal (valuationOf q) (1716)) (literal (valuationOf q) (1718)) (countLit q [-113, -116]) (countLit q [-119, -120]) (count1718 q) 1 (meaning1716 q) (meaning1718 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1718 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1719 = true := by
  have hs : count1718 q = (countLit q [-113, -116]) + (countLit q [-119, -120]) := List.countP_append (p := literal q) (l₁ := [-113, -116]) (l₂ := [-119, -120])
  have hm := merge_right (literal (valuationOf q) (1717)) (literal (valuationOf q) (1719)) (countLit q [-113, -116]) (countLit q [-119, -120]) (count1718 q) 2 (meaning1717 q) (meaning1719 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1719 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1718 = true := by
  have hs : count1718 q = (countLit q [-113, -116]) + (countLit q [-119, -120]) := List.countP_append (p := literal q) (l₁ := [-113, -116]) (l₂ := [-119, -120])
  have hm := merge_left (literal (valuationOf q) (1714)) (literal (valuationOf q) (1718)) (countLit q [-113, -116]) (countLit q [-119, -120]) (count1718 q) 1 (meaning1714 q) (meaning1718 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1718 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E258.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112258
