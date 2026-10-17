import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1724 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_left (literal (valuationOf q) (1712)) (literal (valuationOf q) (1724)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 2 (meaning1712 q) (meaning1724 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1724 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1725 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1725)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 2 1 (meaning1712 q) (meaning1719 q) (meaning1725 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1719 = false ∨ valuation q 1725 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1726 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1726)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 2 2 (meaning1712 q) (meaning1720 q) (meaning1726 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1720 = false ∨ valuation q 1726 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1712 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1727 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1712)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1727)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 2 3 (meaning1712 q) (meaning1721 q) (meaning1727 q) hs
  change valuationOf q 1712 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1712 = false ∨ valuation q 1721 = false ∨ valuation q 1727 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1726 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1726)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 3 1 (meaning1713 q) (meaning1719 q) (meaning1726 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1719 = false ∨ valuation q 1726 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1727 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1727)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 3 2 (meaning1713 q) (meaning1720 q) (meaning1727 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1720 = false ∨ valuation q 1727 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1713 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1728 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1713)) (literal (valuationOf q) (1721)) (literal (valuationOf q) (1728)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 3 3 (meaning1713 q) (meaning1721 q) (meaning1728 q) hs
  change valuationOf q 1713 = false ∨ valuationOf q 1721 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1713 = false ∨ valuation q 1721 = false ∨ valuation q 1728 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1727 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1719)) (literal (valuationOf q) (1727)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 4 1 (meaning1714 q) (meaning1719 q) (meaning1727 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1719 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1719 = false ∨ valuation q 1727 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1714 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1728 = true := by
  have hs : count1723 q = (countLit q [-63, -64, -67, -70]) + (countLit q [-72, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70]) (l₂ := [-72, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1714)) (literal (valuationOf q) (1720)) (literal (valuationOf q) (1728)) (countLit q [-63, -64, -67, -70]) (countLit q [-72, -73, -75, -76]) (count1723 q) 4 2 (meaning1714 q) (meaning1720 q) (meaning1728 q) hs
  change valuationOf q 1714 = false ∨ valuationOf q 1720 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1714 = false ∨ valuation q 1720 = false ∨ valuation q 1728 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1731 = true := by
  have hs : count1731 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1731)) (countLit q [-80]) (countLit q [-82]) (count1731 q) 1 (meaningNeg82 q) (meaning1731 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1731 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1731 = true := by
  have hs : count1731 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1731)) (countLit q [-80]) (countLit q [-82]) (count1731 q) 1 (meaningNeg80 q) (meaning1731 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1731 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1732 = true := by
  have hs : count1731 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1732)) (countLit q [-80]) (countLit q [-82]) (count1731 q) 1 1 (meaningNeg80 q) (meaningNeg82 q) (meaning1732 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1732 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 1732 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1733)) (countLit q [-83]) (countLit q [-84]) (count1733 q) 1 (meaningNeg84 q) (meaning1733 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1733 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1733 = true := by
  have hs : count1733 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1733)) (countLit q [-83]) (countLit q [-84]) (count1733 q) 1 (meaningNeg83 q) (meaning1733 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1733 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 84 = true ∨ valuationOf q 1734 = true := by
  have hs : count1733 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (1734)) (countLit q [-83]) (countLit q [-84]) (count1733 q) 1 1 (meaningNeg83 q) (meaningNeg84 q) (meaning1734 q) hs
  change (! (valuationOf q 83)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 1734 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-80, -82]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-80, -82]) (l₂ := [-83, -84])
  have hm := merge_right (literal (valuationOf q) (1733)) (literal (valuationOf q) (1735)) (countLit q [-80, -82]) (countLit q [-83, -84]) (count1735 q) 1 (meaning1733 q) (meaning1735 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1735 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-80, -82]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-80, -82]) (l₂ := [-83, -84])
  have hm := merge_right (literal (valuationOf q) (1734)) (literal (valuationOf q) (1736)) (countLit q [-80, -82]) (countLit q [-83, -84]) (count1735 q) 2 (meaning1734 q) (meaning1736 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1736 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1735 = true := by
  have hs : count1735 q = (countLit q [-80, -82]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-80, -82]) (l₂ := [-83, -84])
  have hm := merge_left (literal (valuationOf q) (1731)) (literal (valuationOf q) (1735)) (countLit q [-80, -82]) (countLit q [-83, -84]) (count1735 q) 1 (meaning1731 q) (meaning1735 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1735 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1731 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-80, -82]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-80, -82]) (l₂ := [-83, -84])
  have hm := merge_two (literal (valuationOf q) (1731)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1736)) (countLit q [-80, -82]) (countLit q [-83, -84]) (count1735 q) 1 1 (meaning1731 q) (meaning1733 q) (meaning1736 q) hs
  change valuationOf q 1731 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1731 = false ∨ valuation q 1733 = false ∨ valuation q 1736 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1732 = false ∨ valuationOf q 1736 = true := by
  have hs : count1735 q = (countLit q [-80, -82]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-80, -82]) (l₂ := [-83, -84])
  have hm := merge_left (literal (valuationOf q) (1732)) (literal (valuationOf q) (1736)) (countLit q [-80, -82]) (countLit q [-83, -84]) (count1735 q) 2 (meaning1732 q) (meaning1736 q) hs
  change valuationOf q 1732 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1732 = false ∨ valuation q 1736 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1739 = true := by
  have hs : count1739 q = (countLit q [-87]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1739)) (countLit q [-87]) (countLit q [-88]) (count1739 q) 1 (meaningNeg88 q) (meaning1739 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1739 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1741 = true := by
  have hs : count1741 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1741)) (countLit q [-92]) (countLit q [-93]) (count1741 q) 1 (meaningNeg93 q) (meaning1741 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1741 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1741 = true := by
  have hs : count1741 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1741)) (countLit q [-92]) (countLit q [-93]) (count1741 q) 1 (meaningNeg92 q) (meaning1741 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1741 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1741 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1742 = true := by
  have hs : count1741 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1742)) (countLit q [-92]) (countLit q [-93]) (count1741 q) 1 1 (meaningNeg92 q) (meaningNeg93 q) (meaning1742 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1742 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 93 = true ∨ valuation q 1742 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1743 = true := by
  have hs : count1743 q = (countLit q [-87, -88]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -88]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1741)) (literal (valuationOf q) (1743)) (countLit q [-87, -88]) (countLit q [-92, -93]) (count1743 q) 1 (meaning1741 q) (meaning1743 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1743 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1744 = true := by
  have hs : count1743 q = (countLit q [-87, -88]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -88]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1742)) (literal (valuationOf q) (1744)) (countLit q [-87, -88]) (countLit q [-92, -93]) (count1743 q) 2 (meaning1742 q) (meaning1744 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1744 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1743 = true := by
  have hs : count1743 q = (countLit q [-87, -88]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -88]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (1739)) (literal (valuationOf q) (1743)) (countLit q [-87, -88]) (countLit q [-92, -93]) (count1743 q) 1 (meaning1739 q) (meaning1743 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1743 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1744 = true := by
  have hs : count1743 q = (countLit q [-87, -88]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -88]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1741)) (literal (valuationOf q) (1744)) (countLit q [-87, -88]) (countLit q [-92, -93]) (count1743 q) 1 1 (meaning1739 q) (meaning1741 q) (meaning1744 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1741 = false ∨ valuationOf q 1744 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1741 = false ∨ valuation q 1744 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1745 = true := by
  have hs : count1743 q = (countLit q [-87, -88]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-87, -88]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1742)) (literal (valuationOf q) (1745)) (countLit q [-87, -88]) (countLit q [-92, -93]) (count1743 q) 1 2 (meaning1739 q) (meaning1742 q) (meaning1745 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1742 = false ∨ valuationOf q 1745 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1742 = false ∨ valuation q 1745 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1743 = false ∨ valuationOf q 1747 = true := by
  have hs : count1747 q = (countLit q [-80, -82, -83, -84]) + (countLit q [-87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -83, -84]) (l₂ := [-87, -88, -92, -93])
  have hm := merge_right (literal (valuationOf q) (1743)) (literal (valuationOf q) (1747)) (countLit q [-80, -82, -83, -84]) (countLit q [-87, -88, -92, -93]) (count1747 q) 1 (meaning1743 q) (meaning1747 q) hs
  change valuationOf q 1743 = false ∨ valuationOf q 1747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1743 = false ∨ valuation q 1747 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1744 = false ∨ valuationOf q 1748 = true := by
  have hs : count1747 q = (countLit q [-80, -82, -83, -84]) + (countLit q [-87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -83, -84]) (l₂ := [-87, -88, -92, -93])
  have hm := merge_right (literal (valuationOf q) (1744)) (literal (valuationOf q) (1748)) (countLit q [-80, -82, -83, -84]) (countLit q [-87, -88, -92, -93]) (count1747 q) 2 (meaning1744 q) (meaning1748 q) hs
  change valuationOf q 1744 = false ∨ valuationOf q 1748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1744 = false ∨ valuation q 1748 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1749 = true := by
  have hs : count1747 q = (countLit q [-80, -82, -83, -84]) + (countLit q [-87, -88, -92, -93]) := List.countP_append (p := literal q) (l₁ := [-80, -82, -83, -84]) (l₂ := [-87, -88, -92, -93])
  have hm := merge_right (literal (valuationOf q) (1745)) (literal (valuationOf q) (1749)) (countLit q [-80, -82, -83, -84]) (countLit q [-87, -88, -92, -93]) (count1747 q) 3 (meaning1745 q) (meaning1749 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1749 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E036.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112036
