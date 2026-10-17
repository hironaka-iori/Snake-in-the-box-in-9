import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 92 = true ∨ valuationOf q 1640 = true := by
  have hs : count1639 q = (countLit q [-90]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-92])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (-92)) (literal (valuationOf q) (1640)) (countLit q [-90]) (countLit q [-92]) (count1639 q) 1 1 (meaningNeg90 q) (meaningNeg92 q) (meaning1640 q) hs
  change (! (valuationOf q 90)) = false ∨ (! (valuationOf q 92)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 92 = true ∨ valuation q 1640 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_right (literal (valuationOf q) (-95)) (literal (valuationOf q) (1641)) (countLit q [-94]) (countLit q [-95]) (count1641 q) 1 (meaningNeg95 q) (meaning1641 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1641 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1641)) (countLit q [-94]) (countLit q [-95]) (count1641 q) 1 (meaningNeg94 q) (meaning1641 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1641 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 95 = true ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-95)) (literal (valuationOf q) (1642)) (countLit q [-94]) (countLit q [-95]) (count1641 q) 1 1 (meaningNeg94 q) (meaningNeg95 q) (meaning1642 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 95)) = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 95 = true ∨ valuation q 1642 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-90, -92]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -92]) (l₂ := [-94, -95])
  have hm := merge_right (literal (valuationOf q) (1641)) (literal (valuationOf q) (1643)) (countLit q [-90, -92]) (countLit q [-94, -95]) (count1643 q) 1 (meaning1641 q) (meaning1643 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1643 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-90, -92]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -92]) (l₂ := [-94, -95])
  have hm := merge_right (literal (valuationOf q) (1642)) (literal (valuationOf q) (1644)) (countLit q [-90, -92]) (countLit q [-94, -95]) (count1643 q) 2 (meaning1642 q) (meaning1644 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1644 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-90, -92]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -92]) (l₂ := [-94, -95])
  have hm := merge_left (literal (valuationOf q) (1639)) (literal (valuationOf q) (1643)) (countLit q [-90, -92]) (countLit q [-94, -95]) (count1643 q) 1 (meaning1639 q) (meaning1643 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1643 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-90, -92]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -92]) (l₂ := [-94, -95])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1644)) (countLit q [-90, -92]) (countLit q [-94, -95]) (count1643 q) 1 1 (meaning1639 q) (meaning1641 q) (meaning1644 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = false ∨ valuation q 1644 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1645 = true := by
  have hs : count1643 q = (countLit q [-90, -92]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -92]) (l₂ := [-94, -95])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1645)) (countLit q [-90, -92]) (countLit q [-94, -95]) (count1643 q) 1 2 (meaning1639 q) (meaning1642 q) (meaning1645 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1642 = false ∨ valuation q 1645 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-90, -92]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -92]) (l₂ := [-94, -95])
  have hm := merge_left (literal (valuationOf q) (1640)) (literal (valuationOf q) (1644)) (countLit q [-90, -92]) (countLit q [-94, -95]) (count1643 q) 2 (meaning1640 q) (meaning1644 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1644 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1643 q = (countLit q [-90, -92]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -92]) (l₂ := [-94, -95])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-90, -92]) (countLit q [-94, -95]) (count1643 q) 2 1 (meaning1640 q) (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1641 = false ∨ valuation q 1645 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1646 = true := by
  have hs : count1643 q = (countLit q [-90, -92]) + (countLit q [-94, -95]) := List.countP_append (p := literal q) (l₁ := [-90, -92]) (l₂ := [-94, -95])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1646)) (countLit q [-90, -92]) (countLit q [-94, -95]) (count1643 q) 2 2 (meaning1640 q) (meaning1642 q) (meaning1646 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1642 = false ∨ valuation q 1646 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1647 = true := by
  have hs : count1647 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1647)) (countLit q [-98]) (countLit q [-99]) (count1647 q) 1 (meaningNeg99 q) (meaning1647 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1647 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1647 = true := by
  have hs : count1647 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1647)) (countLit q [-98]) (countLit q [-99]) (count1647 q) 1 (meaningNeg98 q) (meaning1647 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1647 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 99 = true ∨ valuationOf q 1648 = true := by
  have hs : count1647 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-99)) (literal (valuationOf q) (1648)) (countLit q [-98]) (countLit q [-99]) (count1647 q) 1 1 (meaningNeg98 q) (meaningNeg99 q) (meaning1648 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 99)) = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 99 = true ∨ valuation q 1648 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1649 = true := by
  have hs : count1649 q = (countLit q [-105]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1649)) (countLit q [-105]) (countLit q [-106]) (count1649 q) 1 (meaningNeg106 q) (meaning1649 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1649 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1649 = true := by
  have hs : count1649 q = (countLit q [-105]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106])
  have hm := merge_left (literal (valuationOf q) (-105)) (literal (valuationOf q) (1649)) (countLit q [-105]) (countLit q [-106]) (count1649 q) 1 (meaningNeg105 q) (meaning1649 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1649 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 106 = true ∨ valuationOf q 1650 = true := by
  have hs : count1649 q = (countLit q [-105]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106])
  have hm := merge_two (literal (valuationOf q) (-105)) (literal (valuationOf q) (-106)) (literal (valuationOf q) (1650)) (countLit q [-105]) (countLit q [-106]) (count1649 q) 1 1 (meaningNeg105 q) (meaningNeg106 q) (meaning1650 q) hs
  change (! (valuationOf q 105)) = false ∨ (! (valuationOf q 106)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 1650 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1651 = true := by
  have hs : count1651 q = (countLit q [-98, -99]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-105, -106])
  have hm := merge_right (literal (valuationOf q) (1649)) (literal (valuationOf q) (1651)) (countLit q [-98, -99]) (countLit q [-105, -106]) (count1651 q) 1 (meaning1649 q) (meaning1651 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1651 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1652 = true := by
  have hs : count1651 q = (countLit q [-98, -99]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-105, -106])
  have hm := merge_right (literal (valuationOf q) (1650)) (literal (valuationOf q) (1652)) (countLit q [-98, -99]) (countLit q [-105, -106]) (count1651 q) 2 (meaning1650 q) (meaning1652 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1652 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1651 = true := by
  have hs : count1651 q = (countLit q [-98, -99]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-105, -106])
  have hm := merge_left (literal (valuationOf q) (1647)) (literal (valuationOf q) (1651)) (countLit q [-98, -99]) (countLit q [-105, -106]) (count1651 q) 1 (meaning1647 q) (meaning1651 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1651 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1652 = true := by
  have hs : count1651 q = (countLit q [-98, -99]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-105, -106])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1652)) (countLit q [-98, -99]) (countLit q [-105, -106]) (count1651 q) 1 1 (meaning1647 q) (meaning1649 q) (meaning1652 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1649 = false ∨ valuation q 1652 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1653 = true := by
  have hs : count1651 q = (countLit q [-98, -99]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-105, -106])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1653)) (countLit q [-98, -99]) (countLit q [-105, -106]) (count1651 q) 1 2 (meaning1647 q) (meaning1650 q) (meaning1653 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1650 = false ∨ valuation q 1653 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1652 = true := by
  have hs : count1651 q = (countLit q [-98, -99]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-105, -106])
  have hm := merge_left (literal (valuationOf q) (1648)) (literal (valuationOf q) (1652)) (countLit q [-98, -99]) (countLit q [-105, -106]) (count1651 q) 2 (meaning1648 q) (meaning1652 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1652 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1653 = true := by
  have hs : count1651 q = (countLit q [-98, -99]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-105, -106])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1653)) (countLit q [-98, -99]) (countLit q [-105, -106]) (count1651 q) 2 1 (meaning1648 q) (meaning1649 q) (meaning1653 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1649 = false ∨ valuation q 1653 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1654 = true := by
  have hs : count1651 q = (countLit q [-98, -99]) + (countLit q [-105, -106]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-105, -106])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1654)) (countLit q [-98, -99]) (countLit q [-105, -106]) (count1651 q) 2 2 (meaning1648 q) (meaning1650 q) (meaning1654 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1650 = false ∨ valuation q 1654 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_right (literal (valuationOf q) (1651)) (literal (valuationOf q) (1655)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 1 (meaning1651 q) (meaning1655 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1655 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_right (literal (valuationOf q) (1652)) (literal (valuationOf q) (1656)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 2 (meaning1652 q) (meaning1656 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1656 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_right (literal (valuationOf q) (1653)) (literal (valuationOf q) (1657)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 3 (meaning1653 q) (meaning1657 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1657 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_right (literal (valuationOf q) (1654)) (literal (valuationOf q) (1658)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 4 (meaning1654 q) (meaning1658 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1658 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_left (literal (valuationOf q) (1643)) (literal (valuationOf q) (1655)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 1 (meaning1643 q) (meaning1655 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1655 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1656)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 1 1 (meaning1643 q) (meaning1651 q) (meaning1656 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1651 = false ∨ valuation q 1656 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E040.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112040
