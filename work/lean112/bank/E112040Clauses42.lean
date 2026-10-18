import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1657)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 1 2 (meaning1643 q) (meaning1652 q) (meaning1657 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1652 = false ∨ valuation q 1657 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1658)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 1 3 (meaning1643 q) (meaning1653 q) (meaning1658 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1653 = false ∨ valuation q 1658 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1659)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 1 4 (meaning1643 q) (meaning1654 q) (meaning1659 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1654 = false ∨ valuation q 1659 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_left (literal (valuationOf q) (1644)) (literal (valuationOf q) (1656)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 2 (meaning1644 q) (meaning1656 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1656 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1657)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 2 1 (meaning1644 q) (meaning1651 q) (meaning1657 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1651 = false ∨ valuation q 1657 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1658)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 2 2 (meaning1644 q) (meaning1652 q) (meaning1658 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1652 = false ∨ valuation q 1658 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1659)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 2 3 (meaning1644 q) (meaning1653 q) (meaning1659 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1653 = false ∨ valuation q 1659 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_left (literal (valuationOf q) (1645)) (literal (valuationOf q) (1657)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 3 (meaning1645 q) (meaning1657 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1657 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1658)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 3 1 (meaning1645 q) (meaning1651 q) (meaning1658 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1651 = false ∨ valuation q 1658 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1659)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 3 2 (meaning1645 q) (meaning1652 q) (meaning1659 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1652 = false ∨ valuation q 1659 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1660)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 3 3 (meaning1645 q) (meaning1653 q) (meaning1660 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1653 = false ∨ valuation q 1660 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1659 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1659)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 4 1 (meaning1646 q) (meaning1651 q) (meaning1659 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1651 = false ∨ valuation q 1659 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1660 = true := by
  have hs : count1655 q = (countLit q [-90, -92, -94, -95]) + (countLit q [-98, -99, -105, -106]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -94, -95]) (l₂ := [-98, -99, -105, -106])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1660)) (countLit q [-90, -92, -94, -95]) (countLit q [-98, -99, -105, -106]) (count1655 q) 4 2 (meaning1646 q) (meaning1652 q) (meaning1660 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1652 = false ∨ valuation q 1660 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1663 = true := by
  have hs : count1663 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_right (literal (valuationOf q) (-110)) (literal (valuationOf q) (1663)) (countLit q [-109]) (countLit q [-110]) (count1663 q) 1 (meaningNeg110 q) (meaning1663 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1663 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1663 = true := by
  have hs : count1663 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-109)) (literal (valuationOf q) (1663)) (countLit q [-109]) (countLit q [-110]) (count1663 q) 1 (meaningNeg109 q) (meaning1663 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1663 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 110 = true ∨ valuationOf q 1664 = true := by
  have hs : count1663 q = (countLit q [-109]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-109]) (l₂ := [-110])
  have hm := merge_two (literal (valuationOf q) (-109)) (literal (valuationOf q) (-110)) (literal (valuationOf q) (1664)) (countLit q [-109]) (countLit q [-110]) (count1663 q) 1 1 (meaningNeg109 q) (meaningNeg110 q) (meaning1664 q) hs
  change (! (valuationOf q 109)) = false ∨ (! (valuationOf q 110)) = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 110 = true ∨ valuation q 1664 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1665 = true := by
  have hs : count1665 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_right (literal (valuationOf q) (-113)) (literal (valuationOf q) (1665)) (countLit q [-111]) (countLit q [-113]) (count1665 q) 1 (meaningNeg113 q) (meaning1665 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1665 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1665 = true := by
  have hs : count1665 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1665)) (countLit q [-111]) (countLit q [-113]) (count1665 q) 1 (meaningNeg111 q) (meaning1665 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1665 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 113 = true ∨ valuationOf q 1666 = true := by
  have hs : count1665 q = (countLit q [-111]) + (countLit q [-113]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-113])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-113)) (literal (valuationOf q) (1666)) (countLit q [-111]) (countLit q [-113]) (count1665 q) 1 1 (meaningNeg111 q) (meaningNeg113 q) (meaning1666 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 113)) = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 113 = true ∨ valuation q 1666 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1667 = true := by
  have hs : count1667 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_right (literal (valuationOf q) (1665)) (literal (valuationOf q) (1667)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1667 q) 1 (meaning1665 q) (meaning1667 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1667 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1668 = true := by
  have hs : count1667 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_right (literal (valuationOf q) (1666)) (literal (valuationOf q) (1668)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1667 q) 2 (meaning1666 q) (meaning1668 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1668 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1667 = true := by
  have hs : count1667 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_left (literal (valuationOf q) (1663)) (literal (valuationOf q) (1667)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1667 q) 1 (meaning1663 q) (meaning1667 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1667 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1668 = true := by
  have hs : count1667 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1668)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1667 q) 1 1 (meaning1663 q) (meaning1665 q) (meaning1668 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1665 = false ∨ valuation q 1668 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1669 = true := by
  have hs : count1667 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1669)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1667 q) 1 2 (meaning1663 q) (meaning1666 q) (meaning1669 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1666 = false ∨ valuation q 1669 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1668 = true := by
  have hs : count1667 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_left (literal (valuationOf q) (1664)) (literal (valuationOf q) (1668)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1667 q) 2 (meaning1664 q) (meaning1668 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1668 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1669 = true := by
  have hs : count1667 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1669)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1667 q) 2 1 (meaning1664 q) (meaning1665 q) (meaning1669 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1665 = false ∨ valuation q 1669 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1670 = true := by
  have hs : count1667 q = (countLit q [-109, -110]) + (countLit q [-111, -113]) := List.countP_append (p := literal q) (l₁ := [-109, -110]) (l₂ := [-111, -113])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1670)) (countLit q [-109, -110]) (countLit q [-111, -113]) (count1667 q) 2 2 (meaning1664 q) (meaning1666 q) (meaning1670 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1666 = false ∨ valuation q 1670 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1671 = true := by
  have hs : count1671 q = (countLit q [-115]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-116])
  have hm := merge_right (literal (valuationOf q) (-116)) (literal (valuationOf q) (1671)) (countLit q [-115]) (countLit q [-116]) (count1671 q) 1 (meaningNeg116 q) (meaning1671 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1671 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1671 = true := by
  have hs : count1671 q = (countLit q [-115]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-116])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1671)) (countLit q [-115]) (countLit q [-116]) (count1671 q) 1 (meaningNeg115 q) (meaning1671 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1671 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 116 = true ∨ valuationOf q 1672 = true := by
  have hs : count1671 q = (countLit q [-115]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-116])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-116)) (literal (valuationOf q) (1672)) (countLit q [-115]) (countLit q [-116]) (count1671 q) 1 1 (meaningNeg115 q) (meaningNeg116 q) (meaning1672 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 116)) = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 1672 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 1673 = true := by
  have hs : count1673 q = (countLit q [-117]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-117]) (l₂ := [-120])
  have hm := merge_right (literal (valuationOf q) (-120)) (literal (valuationOf q) (1673)) (countLit q [-117]) (countLit q [-120]) (count1673 q) 1 (meaningNeg120 q) (meaning1673 q) hs
  change (! (valuationOf q 120)) = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 1673 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1675 = true := by
  have hs : count1675 q = (countLit q [-115, -116]) + (countLit q [-117, -120]) := List.countP_append (p := literal q) (l₁ := [-115, -116]) (l₂ := [-117, -120])
  have hm := merge_right (literal (valuationOf q) (1673)) (literal (valuationOf q) (1675)) (countLit q [-115, -116]) (countLit q [-117, -120]) (count1675 q) 1 (meaning1673 q) (meaning1675 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1675 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E040.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112040
