import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1719 = true := by
  have hs : count1718 q = (countLit q [-113, -116]) + (countLit q [-119, -120]) := List.countP_append (p := literal q) (l₁ := [-113, -116]) (l₂ := [-119, -120])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1719)) (countLit q [-113, -116]) (countLit q [-119, -120]) (count1718 q) 1 1 (meaning1714 q) (meaning1716 q) (meaning1719 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1716 = false ∨ valuation q 1719 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1719 = true := by
  have hs : count1718 q = (countLit q [-113, -116]) + (countLit q [-119, -120]) := List.countP_append (p := literal q) (l₁ := [-113, -116]) (l₂ := [-119, -120])
  have hm := merge_left (literal (valuationOf q) (1715)) (literal (valuationOf q) (1719)) (countLit q [-113, -116]) (countLit q [-119, -120]) (count1718 q) 2 (meaning1715 q) (meaning1719 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1719 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1720 = true := by
  have hs : count1718 q = (countLit q [-113, -116]) + (countLit q [-119, -120]) := List.countP_append (p := literal q) (l₁ := [-113, -116]) (l₂ := [-119, -120])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1720)) (countLit q [-113, -116]) (countLit q [-119, -120]) (count1718 q) 2 1 (meaning1715 q) (meaning1716 q) (meaning1720 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1716 = false ∨ valuation q 1720 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1722 = true := by
  have hs : count1722 q = (countLit q [-107, -108, -111, -112]) + (countLit q [-113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -111, -112]) (l₂ := [-113, -116, -119, -120])
  have hm := merge_left (literal (valuationOf q) (1710)) (literal (valuationOf q) (1722)) (countLit q [-107, -108, -111, -112]) (countLit q [-113, -116, -119, -120]) (count1722 q) 1 (meaning1710 q) (meaning1722 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1722 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1723 = true := by
  have hs : count1722 q = (countLit q [-107, -108, -111, -112]) + (countLit q [-113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -111, -112]) (l₂ := [-113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1710)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1723)) (countLit q [-107, -108, -111, -112]) (countLit q [-113, -116, -119, -120]) (count1722 q) 1 1 (meaning1710 q) (meaning1718 q) (meaning1723 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1718 = false ∨ valuation q 1723 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1724 = true := by
  have hs : count1722 q = (countLit q [-107, -108, -111, -112]) + (countLit q [-113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -111, -112]) (l₂ := [-113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1710)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1724)) (countLit q [-107, -108, -111, -112]) (countLit q [-113, -116, -119, -120]) (count1722 q) 1 2 (meaning1710 q) (meaning1719 q) (meaning1724 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1719 = false ∨ valuation q 1724 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1725 = true := by
  have hs : count1722 q = (countLit q [-107, -108, -111, -112]) + (countLit q [-113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -111, -112]) (l₂ := [-113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1710)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1725)) (countLit q [-107, -108, -111, -112]) (countLit q [-113, -116, -119, -120]) (count1722 q) 1 3 (meaning1710 q) (meaning1720 q) (meaning1725 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1720 = false ∨ valuation q 1725 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1723 = true := by
  have hs : count1722 q = (countLit q [-107, -108, -111, -112]) + (countLit q [-113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -111, -112]) (l₂ := [-113, -116, -119, -120])
  have hm := merge_left (literal (valuationOf q) (1711)) (literal (valuationOf q) (1723)) (countLit q [-107, -108, -111, -112]) (countLit q [-113, -116, -119, -120]) (count1722 q) 2 (meaning1711 q) (meaning1723 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1723 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1724 = true := by
  have hs : count1722 q = (countLit q [-107, -108, -111, -112]) + (countLit q [-113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -111, -112]) (l₂ := [-113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1724)) (countLit q [-107, -108, -111, -112]) (countLit q [-113, -116, -119, -120]) (count1722 q) 2 1 (meaning1711 q) (meaning1718 q) (meaning1724 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1718 = false ∨ valuation q 1724 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1725 = true := by
  have hs : count1722 q = (countLit q [-107, -108, -111, -112]) + (countLit q [-113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -111, -112]) (l₂ := [-113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1725)) (countLit q [-107, -108, -111, -112]) (countLit q [-113, -116, -119, -120]) (count1722 q) 2 2 (meaning1711 q) (meaning1719 q) (meaning1725 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1719 = false ∨ valuation q 1725 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1724 = true := by
  have hs : count1722 q = (countLit q [-107, -108, -111, -112]) + (countLit q [-113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -111, -112]) (l₂ := [-113, -116, -119, -120])
  have hm := merge_left (literal (valuationOf q) (1712)) (literal (valuationOf q) (1724)) (countLit q [-107, -108, -111, -112]) (countLit q [-113, -116, -119, -120]) (count1722 q) 3 (meaning1712 q) (meaning1724 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1724 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1725 = true := by
  have hs : count1722 q = (countLit q [-107, -108, -111, -112]) + (countLit q [-113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -111, -112]) (l₂ := [-113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1725)) (countLit q [-107, -108, -111, -112]) (countLit q [-113, -116, -119, -120]) (count1722 q) 3 1 (meaning1712 q) (meaning1718 q) (meaning1725 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1718 = false ∨ valuation q 1725 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1726 = true := by
  have hs : count1722 q = (countLit q [-107, -108, -111, -112]) + (countLit q [-113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -111, -112]) (l₂ := [-113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1726)) (countLit q [-107, -108, -111, -112]) (countLit q [-113, -116, -119, -120]) (count1722 q) 3 2 (meaning1712 q) (meaning1719 q) (meaning1726 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1719 = false ∨ valuation q 1726 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1725 = true := by
  have hs : count1722 q = (countLit q [-107, -108, -111, -112]) + (countLit q [-113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -111, -112]) (l₂ := [-113, -116, -119, -120])
  have hm := merge_left (literal (valuationOf q) (1713)) (literal (valuationOf q) (1725)) (countLit q [-107, -108, -111, -112]) (countLit q [-113, -116, -119, -120]) (count1722 q) 4 (meaning1713 q) (meaning1725 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1725 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1726 = true := by
  have hs : count1722 q = (countLit q [-107, -108, -111, -112]) + (countLit q [-113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-107, -108, -111, -112]) (l₂ := [-113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1726)) (countLit q [-107, -108, -111, -112]) (countLit q [-113, -116, -119, -120]) (count1722 q) 4 1 (meaning1713 q) (meaning1718 q) (meaning1726 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1718 = false ∨ valuation q 1726 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1731 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_right (literal (valuationOf q) (1723)) (literal (valuationOf q) (1731)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 2 (meaning1723 q) (meaning1731 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1731 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1732 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_right (literal (valuationOf q) (1724)) (literal (valuationOf q) (1732)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 3 (meaning1724 q) (meaning1732 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1732 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1733 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_right (literal (valuationOf q) (1725)) (literal (valuationOf q) (1733)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 4 (meaning1725 q) (meaning1733 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1733 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1734 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_right (literal (valuationOf q) (1726)) (literal (valuationOf q) (1734)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 5 (meaning1726 q) (meaning1734 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1734 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1732 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1732)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 1 2 (meaning1699 q) (meaning1723 q) (meaning1732 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1723 = false ∨ valuation q 1732 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1733 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1733)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 1 3 (meaning1699 q) (meaning1724 q) (meaning1733 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1724 = false ∨ valuation q 1733 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1734 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1734)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 1 4 (meaning1699 q) (meaning1725 q) (meaning1734 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1725 = false ∨ valuation q 1734 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1735 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1735)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 1 5 (meaning1699 q) (meaning1726 q) (meaning1735 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1726 = false ∨ valuation q 1735 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1733 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1733)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 2 2 (meaning1700 q) (meaning1723 q) (meaning1733 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1723 = false ∨ valuation q 1733 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1734 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1734)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 2 3 (meaning1700 q) (meaning1724 q) (meaning1734 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1724 = false ∨ valuation q 1734 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1735 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1735)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 2 4 (meaning1700 q) (meaning1725 q) (meaning1735 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1725 = false ∨ valuation q 1735 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1736 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1736)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 2 5 (meaning1700 q) (meaning1726 q) (meaning1736 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1726 = false ∨ valuation q 1736 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1734 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1734)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 3 2 (meaning1701 q) (meaning1723 q) (meaning1734 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1723 = false ∨ valuation q 1734 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1735 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1735)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 3 3 (meaning1701 q) (meaning1724 q) (meaning1735 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1724 = false ∨ valuation q 1735 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1736 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1736)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 3 4 (meaning1701 q) (meaning1725 q) (meaning1736 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1725 = false ∨ valuation q 1736 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1737 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1737)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 3 5 (meaning1701 q) (meaning1726 q) (meaning1737 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1726 = false ∨ valuation q 1737 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1734 = true := by
  have hs : count1730 q = (countLit q [-90, -93, -94, -98, -99, -102, -105]) + (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -98, -99, -102, -105]) (l₂ := [-107, -108, -111, -112, -113, -116, -119, -120])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1734)) (countLit q [-90, -93, -94, -98, -99, -102, -105]) (countLit q [-107, -108, -111, -112, -113, -116, -119, -120]) (count1730 q) 4 1 (meaning1702 q) (meaning1722 q) (meaning1734 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1722 = false ∨ valuation q 1734 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E258.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112258
