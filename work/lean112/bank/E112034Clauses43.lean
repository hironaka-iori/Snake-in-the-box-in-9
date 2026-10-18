import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1705 = true := by
  have hs : count1705 q = (countLit q [-61, -62]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-65, -68])
  have hm := merge_right (literal (valuationOf q) (1703)) (literal (valuationOf q) (1705)) (countLit q [-61, -62]) (countLit q [-65, -68]) (count1705 q) 1 (meaning1703 q) (meaning1705 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1705 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1704 = false ∨ valuationOf q 1706 = true := by
  have hs : count1705 q = (countLit q [-61, -62]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-65, -68])
  have hm := merge_right (literal (valuationOf q) (1704)) (literal (valuationOf q) (1706)) (countLit q [-61, -62]) (countLit q [-65, -68]) (count1705 q) 2 (meaning1704 q) (meaning1706 q) hs
  change valuationOf q 1704 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1706 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1705 = true := by
  have hs : count1705 q = (countLit q [-61, -62]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-65, -68])
  have hm := merge_left (literal (valuationOf q) (1701)) (literal (valuationOf q) (1705)) (countLit q [-61, -62]) (countLit q [-65, -68]) (count1705 q) 1 (meaning1701 q) (meaning1705 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1705 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1705 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1706 = true := by
  have hs : count1705 q = (countLit q [-61, -62]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-65, -68])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1706)) (countLit q [-61, -62]) (countLit q [-65, -68]) (count1705 q) 1 1 (meaning1701 q) (meaning1703 q) (meaning1706 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1703 = false ∨ valuation q 1706 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1707 = true := by
  have hs : count1705 q = (countLit q [-61, -62]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-65, -68])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1707)) (countLit q [-61, -62]) (countLit q [-65, -68]) (count1705 q) 1 2 (meaning1701 q) (meaning1704 q) (meaning1707 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1704 = false ∨ valuation q 1707 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1706 = true := by
  have hs : count1705 q = (countLit q [-61, -62]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-65, -68])
  have hm := merge_left (literal (valuationOf q) (1702)) (literal (valuationOf q) (1706)) (countLit q [-61, -62]) (countLit q [-65, -68]) (count1705 q) 2 (meaning1702 q) (meaning1706 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1706 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1707 = true := by
  have hs : count1705 q = (countLit q [-61, -62]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-65, -68])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1707)) (countLit q [-61, -62]) (countLit q [-65, -68]) (count1705 q) 2 1 (meaning1702 q) (meaning1703 q) (meaning1707 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1703 = false ∨ valuation q 1707 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1708 = true := by
  have hs : count1705 q = (countLit q [-61, -62]) + (countLit q [-65, -68]) := List.countP_append (p := literal q) (l₁ := [-61, -62]) (l₂ := [-65, -68])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1708)) (countLit q [-61, -62]) (countLit q [-65, -68]) (count1705 q) 2 2 (meaning1702 q) (meaning1704 q) (meaning1708 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1704 = false ∨ valuation q 1708 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1709 = true := by
  have hs : count1709 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (1709)) (countLit q [-70]) (countLit q [-72]) (count1709 q) 1 (meaningNeg72 q) (meaning1709 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1709 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1709 = true := by
  have hs : count1709 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1709)) (countLit q [-70]) (countLit q [-72]) (count1709 q) 1 (meaningNeg70 q) (meaning1709 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1709 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 72 = true ∨ valuationOf q 1710 = true := by
  have hs : count1709 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (-72)) (literal (valuationOf q) (1710)) (countLit q [-70]) (countLit q [-72]) (count1709 q) 1 1 (meaningNeg70 q) (meaningNeg72 q) (meaning1710 q) hs
  change (! (valuationOf q 70)) = false ∨ (! (valuationOf q 72)) = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 72 = true ∨ valuation q 1710 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1711)) (countLit q [-73]) (countLit q [-74]) (count1711 q) 1 (meaningNeg74 q) (meaning1711 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1711 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1711)) (countLit q [-73]) (countLit q [-74]) (count1711 q) 1 (meaningNeg73 q) (meaning1711 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1711 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 74 = true ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-73)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (1712)) (countLit q [-73]) (countLit q [-74]) (count1711 q) 1 1 (meaningNeg73 q) (meaningNeg74 q) (meaning1712 q) hs
  change (! (valuationOf q 73)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 74 = true ∨ valuation q 1712 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1713 = true := by
  have hs : count1713 q = (countLit q [-70, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-70, -72]) (l₂ := [-73, -74])
  have hm := merge_right (literal (valuationOf q) (1711)) (literal (valuationOf q) (1713)) (countLit q [-70, -72]) (countLit q [-73, -74]) (count1713 q) 1 (meaning1711 q) (meaning1713 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1713 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1714 = true := by
  have hs : count1713 q = (countLit q [-70, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-70, -72]) (l₂ := [-73, -74])
  have hm := merge_right (literal (valuationOf q) (1712)) (literal (valuationOf q) (1714)) (countLit q [-70, -72]) (countLit q [-73, -74]) (count1713 q) 2 (meaning1712 q) (meaning1714 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1714 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1713 = true := by
  have hs : count1713 q = (countLit q [-70, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-70, -72]) (l₂ := [-73, -74])
  have hm := merge_left (literal (valuationOf q) (1709)) (literal (valuationOf q) (1713)) (countLit q [-70, -72]) (countLit q [-73, -74]) (count1713 q) 1 (meaning1709 q) (meaning1713 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1713 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1714 = true := by
  have hs : count1713 q = (countLit q [-70, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-70, -72]) (l₂ := [-73, -74])
  have hm := merge_two (literal (valuationOf q) (1709)) (literal (valuationOf q) (1711)) (literal (valuationOf q) (1714)) (countLit q [-70, -72]) (countLit q [-73, -74]) (count1713 q) 1 1 (meaning1709 q) (meaning1711 q) (meaning1714 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1711 = false ∨ valuation q 1714 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1709 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1715 = true := by
  have hs : count1713 q = (countLit q [-70, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-70, -72]) (l₂ := [-73, -74])
  have hm := merge_two (literal (valuationOf q) (1709)) (literal (valuationOf q) (1712)) (literal (valuationOf q) (1715)) (countLit q [-70, -72]) (countLit q [-73, -74]) (count1713 q) 1 2 (meaning1709 q) (meaning1712 q) (meaning1715 q) hs
  change valuationOf q 1709 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1709 = false ∨ valuation q 1712 = false ∨ valuation q 1715 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1714 = true := by
  have hs : count1713 q = (countLit q [-70, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-70, -72]) (l₂ := [-73, -74])
  have hm := merge_left (literal (valuationOf q) (1710)) (literal (valuationOf q) (1714)) (countLit q [-70, -72]) (countLit q [-73, -74]) (count1713 q) 2 (meaning1710 q) (meaning1714 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1714 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1715 = true := by
  have hs : count1713 q = (countLit q [-70, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-70, -72]) (l₂ := [-73, -74])
  have hm := merge_two (literal (valuationOf q) (1710)) (literal (valuationOf q) (1711)) (literal (valuationOf q) (1715)) (countLit q [-70, -72]) (countLit q [-73, -74]) (count1713 q) 2 1 (meaning1710 q) (meaning1711 q) (meaning1715 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1711 = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1711 = false ∨ valuation q 1715 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1710 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1716 = true := by
  have hs : count1713 q = (countLit q [-70, -72]) + (countLit q [-73, -74]) := List.countP_append (p := literal q) (l₁ := [-70, -72]) (l₂ := [-73, -74])
  have hm := merge_two (literal (valuationOf q) (1710)) (literal (valuationOf q) (1712)) (literal (valuationOf q) (1716)) (countLit q [-70, -72]) (countLit q [-73, -74]) (count1713 q) 2 2 (meaning1710 q) (meaning1712 q) (meaning1716 q) hs
  change valuationOf q 1710 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1710 = false ∨ valuation q 1712 = false ∨ valuation q 1716 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1718 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_right (literal (valuationOf q) (1714)) (literal (valuationOf q) (1718)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 2 (meaning1714 q) (meaning1718 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1718 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1719 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_right (literal (valuationOf q) (1715)) (literal (valuationOf q) (1719)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 3 (meaning1715 q) (meaning1719 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1719 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 1705 = false ∨ valuationOf q 1717 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_left (literal (valuationOf q) (1705)) (literal (valuationOf q) (1717)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 1 (meaning1705 q) (meaning1717 q) hs
  change valuationOf q 1705 = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1705 = false ∨ valuation q 1717 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1705 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1718 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (1705)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1718)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 1 1 (meaning1705 q) (meaning1713 q) (meaning1718 q) hs
  change valuationOf q 1705 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1705 = false ∨ valuation q 1713 = false ∨ valuation q 1718 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 1705 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1719 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (1705)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1719)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 1 2 (meaning1705 q) (meaning1714 q) (meaning1719 q) hs
  change valuationOf q 1705 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1705 = false ∨ valuation q 1714 = false ∨ valuation q 1719 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 1705 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1720 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (1705)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1720)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 1 3 (meaning1705 q) (meaning1715 q) (meaning1720 q) hs
  change valuationOf q 1705 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 1705 = false ∨ valuation q 1715 = false ∨ valuation q 1720 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 1705 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1721 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (1705)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1721)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 1 4 (meaning1705 q) (meaning1716 q) (meaning1721 q) hs
  change valuationOf q 1705 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1705 = false ∨ valuation q 1716 = false ∨ valuation q 1721 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1718 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_left (literal (valuationOf q) (1706)) (literal (valuationOf q) (1718)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 2 (meaning1706 q) (meaning1718 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1718 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1719 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (1706)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1719)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 2 1 (meaning1706 q) (meaning1713 q) (meaning1719 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1713 = false ∨ valuation q 1719 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1720 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (1706)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1720)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 2 2 (meaning1706 q) (meaning1714 q) (meaning1720 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1714 = false ∨ valuation q 1720 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E034.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112034
