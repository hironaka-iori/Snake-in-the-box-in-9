import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1722 = false ∨ valuationOf q 1726 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1722)) (literal (valuationOf q) (1726)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 2 (meaning1722 q) (meaning1726 q) hs
  change valuationOf q 1722 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1722 = false ∨ valuation q 1726 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1727 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1723)) (literal (valuationOf q) (1727)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 3 (meaning1723 q) (meaning1727 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1727 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1728 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_right (literal (valuationOf q) (1724)) (literal (valuationOf q) (1728)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 4 (meaning1724 q) (meaning1728 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1728 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1725 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1713)) (literal (valuationOf q) (1725)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 1 (meaning1713 q) (meaning1725 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1725 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1726 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1726)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 1 1 (meaning1713 q) (meaning1721 q) (meaning1726 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1721 = false ∨ valuation q 1726 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1727 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1727)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 1 2 (meaning1713 q) (meaning1722 q) (meaning1727 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1722 = false ∨ valuation q 1727 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1728 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1728)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 1 3 (meaning1713 q) (meaning1723 q) (meaning1728 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1723 = false ∨ valuation q 1728 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1729 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1729)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 1 4 (meaning1713 q) (meaning1724 q) (meaning1729 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1724 = false ∨ valuation q 1729 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1726 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1714)) (literal (valuationOf q) (1726)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 2 (meaning1714 q) (meaning1726 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1726 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1727 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1727)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 2 1 (meaning1714 q) (meaning1721 q) (meaning1727 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1721 = false ∨ valuation q 1727 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1728 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1728)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 2 2 (meaning1714 q) (meaning1722 q) (meaning1728 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1722 = false ∨ valuation q 1728 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1729 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1729)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 2 3 (meaning1714 q) (meaning1723 q) (meaning1729 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1723 = false ∨ valuation q 1729 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1730 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1730)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 2 4 (meaning1714 q) (meaning1724 q) (meaning1730 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1724 = false ∨ valuation q 1730 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1727 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1715)) (literal (valuationOf q) (1727)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 3 (meaning1715 q) (meaning1727 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1727 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1728 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1728)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 3 1 (meaning1715 q) (meaning1721 q) (meaning1728 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1721 = false ∨ valuation q 1728 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1729 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1729)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 3 2 (meaning1715 q) (meaning1722 q) (meaning1729 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1722 = false ∨ valuation q 1729 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1730 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1730)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 3 3 (meaning1715 q) (meaning1723 q) (meaning1730 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1723 = false ∨ valuation q 1730 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1731 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1731)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 3 4 (meaning1715 q) (meaning1724 q) (meaning1731 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1724 = false ∨ valuation q 1731 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1728 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1716)) (literal (valuationOf q) (1728)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 4 (meaning1716 q) (meaning1728 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1728 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1729 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1729)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 4 1 (meaning1716 q) (meaning1721 q) (meaning1729 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1721 = false ∨ valuation q 1729 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1730 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1730)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 4 2 (meaning1716 q) (meaning1722 q) (meaning1730 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1722 = false ∨ valuation q 1730 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1731 = true := by
  have hs : count1725 q = (countLit q [-90, -94, -97, -99]) + (countLit q [-100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-90, -94, -97, -99]) (l₂ := [-100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1731)) (countLit q [-90, -94, -97, -99]) (countLit q [-100, -102, -103, -105]) (count1725 q) 4 3 (meaning1716 q) (meaning1723 q) (meaning1731 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1723 = false ∨ valuation q 1731 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-107]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-110])
  have hm := merge_right (literal (valuationOf q) (-110)) (literal (valuationOf q) (1733)) (countLit q [-107]) (countLit q [-110]) (count1733 q) 1 (meaningNeg110 q) (meaning1733 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1733 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-107]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1733)) (countLit q [-107]) (countLit q [-110]) (count1733 q) 1 (meaningNeg107 q) (meaning1733 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1733 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 110 = true ∨ valuationOf q 1734 = true := by
  have hs : count1733 q = (countLit q [-107]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-110])
  have hm := merge_two (literal (valuationOf q) (-107)) (literal (valuationOf q) (-110)) (literal (valuationOf q) (1734)) (countLit q [-107]) (countLit q [-110]) (count1733 q) 1 1 (meaningNeg107 q) (meaningNeg110 q) (meaning1734 q) hs
  change (! (valuationOf q 107)) = false ∨ (! (valuationOf q 110)) = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 110 = true ∨ valuation q 1734 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1735)) (countLit q [-112]) (countLit q [-113]) (count1735 q) 1 (meaningNeg113 q) (meaning1735 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1735 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-112)) (literal (valuationOf q) (1735)) (countLit q [-112]) (countLit q [-113]) (count1735 q) 1 (meaningNeg112 q) (meaning1735 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1735 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-112]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-112)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1736)) (countLit q [-112]) (countLit q [-113]) (count1735 q) 1 1 (meaningNeg112 q) (meaningNeg113 q) (meaning1736 q) hs
  change (! (valuationOf q 112)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 113 = true ∨ valuation q 1736 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1737 = true := by
  have hs : count1737 q = (countLit q [-107, -110]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -110]) (l₂ := [-112, -113])
  have hm := merge_right (literal (valuationOf q) (1735)) (literal (valuationOf q) (1737)) (countLit q [-107, -110]) (countLit q [-112, -113]) (count1737 q) 1 (meaning1735 q) (meaning1737 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1737 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1738 = true := by
  have hs : count1737 q = (countLit q [-107, -110]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -110]) (l₂ := [-112, -113])
  have hm := merge_right (literal (valuationOf q) (1736)) (literal (valuationOf q) (1738)) (countLit q [-107, -110]) (countLit q [-112, -113]) (count1737 q) 2 (meaning1736 q) (meaning1738 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1738 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1737 = true := by
  have hs : count1737 q = (countLit q [-107, -110]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -110]) (l₂ := [-112, -113])
  have hm := merge_left (literal (valuationOf q) (1733)) (literal (valuationOf q) (1737)) (countLit q [-107, -110]) (countLit q [-112, -113]) (count1737 q) 1 (meaning1733 q) (meaning1737 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1737 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1738 = true := by
  have hs : count1737 q = (countLit q [-107, -110]) + (countLit q [-112, -113]) := List.countP_append (p := literal q) (l₁ := [-107, -110]) (l₂ := [-112, -113])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1738)) (countLit q [-107, -110]) (countLit q [-112, -113]) (count1737 q) 1 1 (meaning1733 q) (meaning1735 q) (meaning1738 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1735 = false ∨ valuation q 1738 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E008.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112008
