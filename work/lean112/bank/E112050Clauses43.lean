import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1711 = true := by
  have hs : count1711 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_left (literal (valuationOf q) (1707)) (literal (valuationOf q) (1711)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count1711 q) 1 (meaning1707 q) (meaning1711 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1711 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1711 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1712)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count1711 q) 1 1 (meaning1707 q) (meaning1709 q) (meaning1712 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1709 = false ∨ valuation q 1712 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1713 = true := by
  have hs : count1711 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1713)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count1711 q) 1 2 (meaning1707 q) (meaning1710 q) (meaning1713 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1710 = false ∨ valuation q 1713 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1712 = true := by
  have hs : count1711 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_left (literal (valuationOf q) (1708)) (literal (valuationOf q) (1712)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count1711 q) 2 (meaning1708 q) (meaning1712 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1712 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1712 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1713 = true := by
  have hs : count1711 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_two (literal (valuationOf q) (1708)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1713)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count1711 q) 2 1 (meaning1708 q) (meaning1709 q) (meaning1713 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1713 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1709 = false ∨ valuation q 1713 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1714 = true := by
  have hs : count1711 q = (countLit q [-65, -66]) + (countLit q [-68, -69]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -69])
  have hm := merge_two (literal (valuationOf q) (1708)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1714)) (countLit q [-65, -66]) (countLit q [-68, -69]) (count1711 q) 2 2 (meaning1708 q) (meaning1710 q) (meaning1714 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1714 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1710 = false ∨ valuation q 1714 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1715 = true := by
  have hs : count1715 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1715)) (countLit q [-72]) (countLit q [-73]) (count1715 q) 1 (meaningNeg73 q) (meaning1715 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1715 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1715 = true := by
  have hs : count1715 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1715)) (countLit q [-72]) (countLit q [-73]) (count1715 q) 1 (meaningNeg72 q) (meaning1715 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1715 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1715 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1716 = true := by
  have hs : count1715 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1716)) (countLit q [-72]) (countLit q [-73]) (count1715 q) 1 1 (meaningNeg72 q) (meaningNeg73 q) (meaning1716 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1716 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 73 = true ∨ valuation q 1716 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1717 = true := by
  have hs : count1717 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1717)) (countLit q [-78]) (countLit q [-79]) (count1717 q) 1 (meaningNeg79 q) (meaning1717 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1717 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1717 = true := by
  have hs : count1717 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1717)) (countLit q [-78]) (countLit q [-79]) (count1717 q) 1 (meaningNeg78 q) (meaning1717 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1717 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1717 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1718 = true := by
  have hs : count1717 q = (countLit q [-78]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1718)) (countLit q [-78]) (countLit q [-79]) (count1717 q) 1 1 (meaningNeg78 q) (meaningNeg79 q) (meaning1718 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1718 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 79 = true ∨ valuation q 1718 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 1717 = false ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-78, -79])
  have hm := merge_right (literal (valuationOf q) (1717)) (literal (valuationOf q) (1719)) (countLit q [-72, -73]) (countLit q [-78, -79]) (count1719 q) 1 (meaning1717 q) (meaning1719 q) hs
  change valuationOf q 1717 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 1717 = false ∨ valuation q 1719 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 1718 = false ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-78, -79])
  have hm := merge_right (literal (valuationOf q) (1718)) (literal (valuationOf q) (1720)) (countLit q [-72, -73]) (countLit q [-78, -79]) (count1719 q) 2 (meaning1718 q) (meaning1720 q) hs
  change valuationOf q 1718 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 1718 = false ∨ valuation q 1720 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1719 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-78, -79])
  have hm := merge_left (literal (valuationOf q) (1715)) (literal (valuationOf q) (1719)) (countLit q [-72, -73]) (countLit q [-78, -79]) (count1719 q) 1 (meaning1715 q) (meaning1719 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1719 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1720)) (countLit q [-72, -73]) (countLit q [-78, -79]) (count1719 q) 1 1 (meaning1715 q) (meaning1717 q) (meaning1720 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1717 = false ∨ valuation q 1720 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1715 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1721 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (1715)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1721)) (countLit q [-72, -73]) (countLit q [-78, -79]) (count1719 q) 1 2 (meaning1715 q) (meaning1718 q) (meaning1721 q) hs
  change valuationOf q 1715 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1715 = false ∨ valuation q 1718 = false ∨ valuation q 1721 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1720 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-78, -79])
  have hm := merge_left (literal (valuationOf q) (1716)) (literal (valuationOf q) (1720)) (countLit q [-72, -73]) (countLit q [-78, -79]) (count1719 q) 2 (meaning1716 q) (meaning1720 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1720 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1721 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1721)) (countLit q [-72, -73]) (countLit q [-78, -79]) (count1719 q) 2 1 (meaning1716 q) (meaning1717 q) (meaning1721 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1717 = false ∨ valuation q 1721 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1716 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1722 = true := by
  have hs : count1719 q = (countLit q [-72, -73]) + (countLit q [-78, -79]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-78, -79])
  have hm := merge_two (literal (valuationOf q) (1716)) (literal (valuationOf q) (1718)) (literal (valuationOf q) (1722)) (countLit q [-72, -73]) (countLit q [-78, -79]) (count1719 q) 2 2 (meaning1716 q) (meaning1718 q) (meaning1722 q) hs
  change valuationOf q 1716 = false ∨ valuationOf q 1718 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1716 = false ∨ valuation q 1718 = false ∨ valuation q 1722 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1719 = false ∨ valuationOf q 1723 = true := by
  have hs : count1723 q = (countLit q [-65, -66, -68, -69]) + (countLit q [-72, -73, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69]) (l₂ := [-72, -73, -78, -79])
  have hm := merge_right (literal (valuationOf q) (1719)) (literal (valuationOf q) (1723)) (countLit q [-65, -66, -68, -69]) (countLit q [-72, -73, -78, -79]) (count1723 q) 1 (meaning1719 q) (meaning1723 q) hs
  change valuationOf q 1719 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1719 = false ∨ valuation q 1723 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1720 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-65, -66, -68, -69]) + (countLit q [-72, -73, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69]) (l₂ := [-72, -73, -78, -79])
  have hm := merge_right (literal (valuationOf q) (1720)) (literal (valuationOf q) (1724)) (countLit q [-65, -66, -68, -69]) (countLit q [-72, -73, -78, -79]) (count1723 q) 2 (meaning1720 q) (meaning1724 q) hs
  change valuationOf q 1720 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1720 = false ∨ valuation q 1724 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1721 = false ∨ valuationOf q 1725 = true := by
  have hs : count1723 q = (countLit q [-65, -66, -68, -69]) + (countLit q [-72, -73, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69]) (l₂ := [-72, -73, -78, -79])
  have hm := merge_right (literal (valuationOf q) (1721)) (literal (valuationOf q) (1725)) (countLit q [-65, -66, -68, -69]) (countLit q [-72, -73, -78, -79]) (count1723 q) 3 (meaning1721 q) (meaning1725 q) hs
  change valuationOf q 1721 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1721 = false ∨ valuation q 1725 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1722 = false ∨ valuationOf q 1726 = true := by
  have hs : count1723 q = (countLit q [-65, -66, -68, -69]) + (countLit q [-72, -73, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69]) (l₂ := [-72, -73, -78, -79])
  have hm := merge_right (literal (valuationOf q) (1722)) (literal (valuationOf q) (1726)) (countLit q [-65, -66, -68, -69]) (countLit q [-72, -73, -78, -79]) (count1723 q) 4 (meaning1722 q) (meaning1726 q) hs
  change valuationOf q 1722 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1722 = false ∨ valuation q 1726 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1723 = true := by
  have hs : count1723 q = (countLit q [-65, -66, -68, -69]) + (countLit q [-72, -73, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69]) (l₂ := [-72, -73, -78, -79])
  have hm := merge_left (literal (valuationOf q) (1711)) (literal (valuationOf q) (1723)) (countLit q [-65, -66, -68, -69]) (countLit q [-72, -73, -78, -79]) (count1723 q) 1 (meaning1711 q) (meaning1723 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1723 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-65, -66, -68, -69]) + (countLit q [-72, -73, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69]) (l₂ := [-72, -73, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1724)) (countLit q [-65, -66, -68, -69]) (countLit q [-72, -73, -78, -79]) (count1723 q) 1 1 (meaning1711 q) (meaning1719 q) (meaning1724 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1719 = false ∨ valuation q 1724 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1725 = true := by
  have hs : count1723 q = (countLit q [-65, -66, -68, -69]) + (countLit q [-72, -73, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69]) (l₂ := [-72, -73, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1725)) (countLit q [-65, -66, -68, -69]) (countLit q [-72, -73, -78, -79]) (count1723 q) 1 2 (meaning1711 q) (meaning1720 q) (meaning1725 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1720 = false ∨ valuation q 1725 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1726 = true := by
  have hs : count1723 q = (countLit q [-65, -66, -68, -69]) + (countLit q [-72, -73, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69]) (l₂ := [-72, -73, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1726)) (countLit q [-65, -66, -68, -69]) (countLit q [-72, -73, -78, -79]) (count1723 q) 1 3 (meaning1711 q) (meaning1721 q) (meaning1726 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1721 = false ∨ valuation q 1726 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 1711 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1727 = true := by
  have hs : count1723 q = (countLit q [-65, -66, -68, -69]) + (countLit q [-72, -73, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69]) (l₂ := [-72, -73, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1711)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1727)) (countLit q [-65, -66, -68, -69]) (countLit q [-72, -73, -78, -79]) (count1723 q) 1 4 (meaning1711 q) (meaning1722 q) (meaning1727 q) hs
  change valuationOf q 1711 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1711 = false ∨ valuation q 1722 = false ∨ valuation q 1727 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-65, -66, -68, -69]) + (countLit q [-72, -73, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69]) (l₂ := [-72, -73, -78, -79])
  have hm := merge_left (literal (valuationOf q) (1712)) (literal (valuationOf q) (1724)) (countLit q [-65, -66, -68, -69]) (countLit q [-72, -73, -78, -79]) (count1723 q) 2 (meaning1712 q) (meaning1724 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1724 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1725 = true := by
  have hs : count1723 q = (countLit q [-65, -66, -68, -69]) + (countLit q [-72, -73, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69]) (l₂ := [-72, -73, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1725)) (countLit q [-65, -66, -68, -69]) (countLit q [-72, -73, -78, -79]) (count1723 q) 2 1 (meaning1712 q) (meaning1719 q) (meaning1725 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1719 = false ∨ valuation q 1725 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1726 = true := by
  have hs : count1723 q = (countLit q [-65, -66, -68, -69]) + (countLit q [-72, -73, -78, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -68, -69]) (l₂ := [-72, -73, -78, -79])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1726)) (countLit q [-65, -66, -68, -69]) (countLit q [-72, -73, -78, -79]) (count1723 q) 2 2 (meaning1712 q) (meaning1720 q) (meaning1726 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1720 = false ∨ valuation q 1726 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E050.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112050
