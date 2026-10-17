import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1721 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (1706)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1721)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 2 3 (meaning1706 q) (meaning1715 q) (meaning1721 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1715 = false ∨ valuation q 1721 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1722 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (1706)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1722)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 2 4 (meaning1706 q) (meaning1716 q) (meaning1722 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1716 = false ∨ valuation q 1722 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1719 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_left (literal (valuationOf q) (1707)) (literal (valuationOf q) (1719)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 3 (meaning1707 q) (meaning1719 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1719 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1719 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1720 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1720)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 3 1 (meaning1707 q) (meaning1713 q) (meaning1720 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1720 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1713 = false ∨ valuation q 1720 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1721 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1721)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 3 2 (meaning1707 q) (meaning1714 q) (meaning1721 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1714 = false ∨ valuation q 1721 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1722 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1722)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 3 3 (meaning1707 q) (meaning1715 q) (meaning1722 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1715 = false ∨ valuation q 1722 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1721 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (1708)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1721)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 4 1 (meaning1708 q) (meaning1713 q) (meaning1721 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1721 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1713 = false ∨ valuation q 1721 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 1708 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1722 = true := by
  have hs : count1717 q = (countLit q [-61, -62, -65, -68]) + (countLit q [-70, -72, -73, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68]) (l₂ := [-70, -72, -73, -74])
  have hm := merge_two (literal (valuationOf q) (1708)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1722)) (countLit q [-61, -62, -65, -68]) (countLit q [-70, -72, -73, -74]) (count1717 q) 4 2 (meaning1708 q) (meaning1714 q) (meaning1722 q) hs
  change valuationOf q 1708 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1722 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false ∨ valuation q 1714 = false ∨ valuation q 1722 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1725 = true := by
  have hs : count1725 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1725)) (countLit q [-77]) (countLit q [-79]) (count1725 q) 1 (meaningNeg79 q) (meaning1725 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1725 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1725 = true := by
  have hs : count1725 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1725)) (countLit q [-77]) (countLit q [-79]) (count1725 q) 1 (meaningNeg77 q) (meaning1725 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1725 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1726 = true := by
  have hs : count1725 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1726)) (countLit q [-77]) (countLit q [-79]) (count1725 q) 1 1 (meaningNeg77 q) (meaningNeg79 q) (meaning1726 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 1726 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1727 = true := by
  have hs : count1727 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1727)) (countLit q [-81]) (countLit q [-82]) (count1727 q) 1 (meaningNeg82 q) (meaning1727 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1727 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1727 = true := by
  have hs : count1727 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1727)) (countLit q [-81]) (countLit q [-82]) (count1727 q) 1 (meaningNeg81 q) (meaning1727 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1727 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1728 = true := by
  have hs : count1727 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1728)) (countLit q [-81]) (countLit q [-82]) (count1727 q) 1 1 (meaningNeg81 q) (meaningNeg82 q) (meaning1728 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 82 = true ∨ valuation q 1728 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1729 = true := by
  have hs : count1729 q = (countLit q [-77, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-81, -82])
  have hm := merge_right (literal (valuationOf q) (1727)) (literal (valuationOf q) (1729)) (countLit q [-77, -79]) (countLit q [-81, -82]) (count1729 q) 1 (meaning1727 q) (meaning1729 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1729 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1730 = true := by
  have hs : count1729 q = (countLit q [-77, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-81, -82])
  have hm := merge_right (literal (valuationOf q) (1728)) (literal (valuationOf q) (1730)) (countLit q [-77, -79]) (countLit q [-81, -82]) (count1729 q) 2 (meaning1728 q) (meaning1730 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1730 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1729 = true := by
  have hs : count1729 q = (countLit q [-77, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-81, -82])
  have hm := merge_left (literal (valuationOf q) (1725)) (literal (valuationOf q) (1729)) (countLit q [-77, -79]) (countLit q [-81, -82]) (count1729 q) 1 (meaning1725 q) (meaning1729 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1729 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1730 = true := by
  have hs : count1729 q = (countLit q [-77, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1727)) (literal (valuationOf q) (1730)) (countLit q [-77, -79]) (countLit q [-81, -82]) (count1729 q) 1 1 (meaning1725 q) (meaning1727 q) (meaning1730 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1727 = false ∨ valuation q 1730 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1728 = false ∨ valuationOf q 1731 = true := by
  have hs : count1729 q = (countLit q [-77, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1728)) (literal (valuationOf q) (1731)) (countLit q [-77, -79]) (countLit q [-81, -82]) (count1729 q) 1 2 (meaning1725 q) (meaning1728 q) (meaning1731 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1728 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1728 = false ∨ valuation q 1731 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1730 = true := by
  have hs : count1729 q = (countLit q [-77, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-81, -82])
  have hm := merge_left (literal (valuationOf q) (1726)) (literal (valuationOf q) (1730)) (countLit q [-77, -79]) (countLit q [-81, -82]) (count1729 q) 2 (meaning1726 q) (meaning1730 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1730 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1731 = true := by
  have hs : count1729 q = (countLit q [-77, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1727)) (literal (valuationOf q) (1731)) (countLit q [-77, -79]) (countLit q [-81, -82]) (count1729 q) 2 1 (meaning1726 q) (meaning1727 q) (meaning1731 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1727 = false ∨ valuation q 1731 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1733)) (countLit q [-84]) (countLit q [-86]) (count1733 q) 1 (meaningNeg86 q) (meaning1733 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1733 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1733)) (countLit q [-84]) (countLit q [-86]) (count1733 q) 1 (meaningNeg84 q) (meaning1733 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1733 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1734 = true := by
  have hs : count1733 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1734)) (countLit q [-84]) (countLit q [-86]) (count1733 q) 1 1 (meaningNeg84 q) (meaningNeg86 q) (meaning1734 q) hs
  change (! (valuationOf q 84)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 86 = true ∨ valuation q 1734 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1735)) (countLit q [-92]) (countLit q [-93]) (count1735 q) 1 (meaningNeg93 q) (meaning1735 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1735 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1735)) (countLit q [-92]) (countLit q [-93]) (count1735 q) 1 (meaningNeg92 q) (meaning1735 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1735 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1736)) (countLit q [-92]) (countLit q [-93]) (count1735 q) 1 1 (meaningNeg92 q) (meaningNeg93 q) (meaning1736 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 93 = true ∨ valuation q 1736 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1735 = false ∨ valuationOf q 1737 = true := by
  have hs : count1737 q = (countLit q [-89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1735)) (literal (valuationOf q) (1737)) (countLit q [-89]) (countLit q [-92, -93]) (count1737 q) 1 (meaning1735 q) (meaning1737 q) hs
  change valuationOf q 1735 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1735 = false ∨ valuation q 1737 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1736 = false ∨ valuationOf q 1738 = true := by
  have hs : count1737 q = (countLit q [-89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1736)) (literal (valuationOf q) (1738)) (countLit q [-89]) (countLit q [-92, -93]) (count1737 q) 2 (meaning1736 q) (meaning1738 q) hs
  change valuationOf q 1736 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1736 = false ∨ valuation q 1738 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1737 = true := by
  have hs : count1737 q = (countLit q [-89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1737)) (countLit q [-89]) (countLit q [-92, -93]) (count1737 q) 1 (meaningNeg89 q) (meaning1737 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1737 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1735 = false ∨ valuationOf q 1738 = true := by
  have hs : count1737 q = (countLit q [-89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1738)) (countLit q [-89]) (countLit q [-92, -93]) (count1737 q) 1 1 (meaningNeg89 q) (meaning1735 q) (meaning1738 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1735 = false ∨ valuation q 1738 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1736 = false ∨ valuationOf q 1739 = true := by
  have hs : count1737 q = (countLit q [-89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1739)) (countLit q [-89]) (countLit q [-92, -93]) (count1737 q) 1 2 (meaningNeg89 q) (meaning1736 q) (meaning1739 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1736 = false ∨ valuation q 1739 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E034.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112034
