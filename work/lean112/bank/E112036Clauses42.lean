import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1747 = true := by
  have hs : count1747 q = (countLit q [-80, -82, -83, -84]) + (countLit q [-87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -83, -84]) (l₂ := [-87, -88, -92, -93])
  have hm := merge_left (literal (valuationOf q) (1735)) (literal (valuationOf q) (1747)) (countLit q [-80, -82, -83, -84]) (countLit q [-87, -88, -92, -93]) (count1747 q) 1 (meaning1735 q) (meaning1747 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1747 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1748 = true := by
  have hs : count1747 q = (countLit q [-80, -82, -83, -84]) + (countLit q [-87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -83, -84]) (l₂ := [-87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1748)) (countLit q [-80, -82, -83, -84]) (countLit q [-87, -88, -92, -93]) (count1747 q) 1 1 (meaning1735 q) (meaning1743 q) (meaning1748 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1743 = false ∨ valuation q 1748 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1749 = true := by
  have hs : count1747 q = (countLit q [-80, -82, -83, -84]) + (countLit q [-87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -83, -84]) (l₂ := [-87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1744)) (literal (valuationOf q) (1749)) (countLit q [-80, -82, -83, -84]) (countLit q [-87, -88, -92, -93]) (count1747 q) 1 2 (meaning1735 q) (meaning1744 q) (meaning1749 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1744 = false ∨ valuation q 1749 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1750 = true := by
  have hs : count1747 q = (countLit q [-80, -82, -83, -84]) + (countLit q [-87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -83, -84]) (l₂ := [-87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1735)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1750)) (countLit q [-80, -82, -83, -84]) (countLit q [-87, -88, -92, -93]) (count1747 q) 1 3 (meaning1735 q) (meaning1745 q) (meaning1750 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1745 = false ∨ valuation q 1750 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1748 = true := by
  have hs : count1747 q = (countLit q [-80, -82, -83, -84]) + (countLit q [-87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -83, -84]) (l₂ := [-87, -88, -92, -93])
  have hm := merge_left (literal (valuationOf q) (1736)) (literal (valuationOf q) (1748)) (countLit q [-80, -82, -83, -84]) (countLit q [-87, -88, -92, -93]) (count1747 q) 2 (meaning1736 q) (meaning1748 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1748 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1749 = true := by
  have hs : count1747 q = (countLit q [-80, -82, -83, -84]) + (countLit q [-87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -83, -84]) (l₂ := [-87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1743)) (literal (valuationOf q) (1749)) (countLit q [-80, -82, -83, -84]) (countLit q [-87, -88, -92, -93]) (count1747 q) 2 1 (meaning1736 q) (meaning1743 q) (meaning1749 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1743 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1743 = false ∨ valuation q 1749 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1750 = true := by
  have hs : count1747 q = (countLit q [-80, -82, -83, -84]) + (countLit q [-87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -83, -84]) (l₂ := [-87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1744)) (literal (valuationOf q) (1750)) (countLit q [-80, -82, -83, -84]) (countLit q [-87, -88, -92, -93]) (count1747 q) 2 2 (meaning1736 q) (meaning1744 q) (meaning1750 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1744 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1744 = false ∨ valuation q 1750 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1751 = true := by
  have hs : count1747 q = (countLit q [-80, -82, -83, -84]) + (countLit q [-87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -83, -84]) (l₂ := [-87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1736)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1751)) (countLit q [-80, -82, -83, -84]) (countLit q [-87, -88, -92, -93]) (count1747 q) 2 3 (meaning1736 q) (meaning1745 q) (meaning1751 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1745 = false ∨ valuation q 1751 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1758 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_right (literal (valuationOf q) (1750)) (literal (valuationOf q) (1758)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 4 (meaning1750 q) (meaning1758 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1758 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1756 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1756)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 1 1 (meaning1723 q) (meaning1747 q) (meaning1756 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1747 = false ∨ valuation q 1756 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1757 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1757)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 1 2 (meaning1723 q) (meaning1748 q) (meaning1757 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1748 = false ∨ valuation q 1757 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1758 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1758)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 1 3 (meaning1723 q) (meaning1749 q) (meaning1758 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1749 = false ∨ valuation q 1758 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1759)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 1 4 (meaning1723 q) (meaning1750 q) (meaning1759 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1750 = false ∨ valuation q 1759 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1723 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1723)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1760)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 1 5 (meaning1723 q) (meaning1751 q) (meaning1760 q) hs
  change valuationOf q 1723 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1723 = false ∨ valuation q 1751 = false ∨ valuation q 1760 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1756 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_left (literal (valuationOf q) (1724)) (literal (valuationOf q) (1756)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 2 (meaning1724 q) (meaning1756 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1756 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1757 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1757)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 2 1 (meaning1724 q) (meaning1747 q) (meaning1757 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1747 = false ∨ valuation q 1757 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1758 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1758)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 2 2 (meaning1724 q) (meaning1748 q) (meaning1758 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1748 = false ∨ valuation q 1758 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1759)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 2 3 (meaning1724 q) (meaning1749 q) (meaning1759 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1749 = false ∨ valuation q 1759 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1760)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 2 4 (meaning1724 q) (meaning1750 q) (meaning1760 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1750 = false ∨ valuation q 1760 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1724 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1724)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1761)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 2 5 (meaning1724 q) (meaning1751 q) (meaning1761 q) hs
  change valuationOf q 1724 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1724 = false ∨ valuation q 1751 = false ∨ valuation q 1761 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1757 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_left (literal (valuationOf q) (1725)) (literal (valuationOf q) (1757)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 3 (meaning1725 q) (meaning1757 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1757 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1758 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1758)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 3 1 (meaning1725 q) (meaning1747 q) (meaning1758 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1747 = false ∨ valuation q 1758 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1759)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 3 2 (meaning1725 q) (meaning1748 q) (meaning1759 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1748 = false ∨ valuation q 1759 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1760)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 3 3 (meaning1725 q) (meaning1749 q) (meaning1760 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1749 = false ∨ valuation q 1760 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1761)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 3 4 (meaning1725 q) (meaning1750 q) (meaning1761 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1750 = false ∨ valuation q 1761 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1762)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 3 5 (meaning1725 q) (meaning1751 q) (meaning1762 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1751 = false ∨ valuation q 1762 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1758 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_left (literal (valuationOf q) (1726)) (literal (valuationOf q) (1758)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 4 (meaning1726 q) (meaning1758 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1758 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1759 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1759)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 4 1 (meaning1726 q) (meaning1747 q) (meaning1759 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1747 = false ∨ valuation q 1759 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1760 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1748)) (literal (valuationOf q) (1760)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 4 2 (meaning1726 q) (meaning1748 q) (meaning1760 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1748 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1748 = false ∨ valuation q 1760 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1761 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1761)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 4 3 (meaning1726 q) (meaning1749 q) (meaning1761 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1749 = false ∨ valuation q 1761 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1762 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1762)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 4 4 (meaning1726 q) (meaning1750 q) (meaning1762 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1750 = false ∨ valuation q 1762 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1763 = true := by
  have hs : count1755 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) + (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76]) (l₂ := [-80, -82, -83, -84, -87, -88, -92, -93])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1763)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76]) (countLit q [-80, -82, -83, -84, -87, -88, -92, -93]) (count1755 q) 4 5 (meaning1726 q) (meaning1751 q) (meaning1763 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1751 = false ∨ valuation q 1763 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E036.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112036
