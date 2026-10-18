import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1684 = true := by
  have hs : count1683 q = (countLit q [-75, -76, -78, -80]) + (countLit q [-83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -78, -80]) (l₂ := [-83, -84, -88, -91])
  have hm := merge_left (literal (valuationOf q) (1672)) (literal (valuationOf q) (1684)) (countLit q [-75, -76, -78, -80]) (countLit q [-83, -84, -88, -91]) (count1683 q) 2 (meaning1672 q) (meaning1684 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1684 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1685 = true := by
  have hs : count1683 q = (countLit q [-75, -76, -78, -80]) + (countLit q [-83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -78, -80]) (l₂ := [-83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1685)) (countLit q [-75, -76, -78, -80]) (countLit q [-83, -84, -88, -91]) (count1683 q) 2 1 (meaning1672 q) (meaning1679 q) (meaning1685 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1679 = false ∨ valuation q 1685 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1686 = true := by
  have hs : count1683 q = (countLit q [-75, -76, -78, -80]) + (countLit q [-83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -78, -80]) (l₂ := [-83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1686)) (countLit q [-75, -76, -78, -80]) (countLit q [-83, -84, -88, -91]) (count1683 q) 2 2 (meaning1672 q) (meaning1680 q) (meaning1686 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1680 = false ∨ valuation q 1686 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1685 = true := by
  have hs : count1683 q = (countLit q [-75, -76, -78, -80]) + (countLit q [-83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -78, -80]) (l₂ := [-83, -84, -88, -91])
  have hm := merge_left (literal (valuationOf q) (1673)) (literal (valuationOf q) (1685)) (countLit q [-75, -76, -78, -80]) (countLit q [-83, -84, -88, -91]) (count1683 q) 3 (meaning1673 q) (meaning1685 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1685 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1686 = true := by
  have hs : count1683 q = (countLit q [-75, -76, -78, -80]) + (countLit q [-83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -78, -80]) (l₂ := [-83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1686)) (countLit q [-75, -76, -78, -80]) (countLit q [-83, -84, -88, -91]) (count1683 q) 3 1 (meaning1673 q) (meaning1679 q) (meaning1686 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1679 = false ∨ valuation q 1686 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1685 = false ∨ valuationOf q 1693 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_right (literal (valuationOf q) (1685)) (literal (valuationOf q) (1693)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 3 (meaning1685 q) (meaning1693 q) hs
  change valuationOf q 1685 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1685 = false ∨ valuation q 1693 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1691 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_left (literal (valuationOf q) (1659)) (literal (valuationOf q) (1691)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 1 (meaning1659 q) (meaning1691 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1691 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1691 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1692 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1692)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 1 1 (meaning1659 q) (meaning1683 q) (meaning1692 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1683 = false ∨ valuation q 1692 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1693 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1693)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 1 2 (meaning1659 q) (meaning1684 q) (meaning1693 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1684 = false ∨ valuation q 1693 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1694 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1694)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 1 3 (meaning1659 q) (meaning1685 q) (meaning1694 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1685 = false ∨ valuation q 1694 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1695 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1695)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 1 4 (meaning1659 q) (meaning1686 q) (meaning1695 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1686 = false ∨ valuation q 1695 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1692 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_left (literal (valuationOf q) (1660)) (literal (valuationOf q) (1692)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 2 (meaning1660 q) (meaning1692 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1692 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1692 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1693 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1693)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 2 1 (meaning1660 q) (meaning1683 q) (meaning1693 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1683 = false ∨ valuation q 1693 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1694 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1694)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 2 2 (meaning1660 q) (meaning1684 q) (meaning1694 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1684 = false ∨ valuation q 1694 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1695 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1695)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 2 3 (meaning1660 q) (meaning1685 q) (meaning1695 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1685 = false ∨ valuation q 1695 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1696)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 2 4 (meaning1660 q) (meaning1686 q) (meaning1696 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1686 = false ∨ valuation q 1696 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1693 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_left (literal (valuationOf q) (1661)) (literal (valuationOf q) (1693)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 3 (meaning1661 q) (meaning1693 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1693 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1694 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1694)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 3 1 (meaning1661 q) (meaning1683 q) (meaning1694 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1683 = false ∨ valuation q 1694 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1695 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1695)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 3 2 (meaning1661 q) (meaning1684 q) (meaning1695 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1684 = false ∨ valuation q 1695 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1696)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 3 3 (meaning1661 q) (meaning1685 q) (meaning1696 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1685 = false ∨ valuation q 1696 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1697)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 3 4 (meaning1661 q) (meaning1686 q) (meaning1697 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1686 = false ∨ valuation q 1697 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1694 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_left (literal (valuationOf q) (1662)) (literal (valuationOf q) (1694)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 4 (meaning1662 q) (meaning1694 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1694 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1695 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1695)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 4 1 (meaning1662 q) (meaning1683 q) (meaning1695 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1683 = false ∨ valuation q 1695 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1696)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 4 2 (meaning1662 q) (meaning1684 q) (meaning1696 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1684 = false ∨ valuation q 1696 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1697)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 4 3 (meaning1662 q) (meaning1685 q) (meaning1697 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1685 = false ∨ valuation q 1697 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1695 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_left (literal (valuationOf q) (1663)) (literal (valuationOf q) (1695)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 5 (meaning1663 q) (meaning1695 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1695 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1696)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 5 1 (meaning1663 q) (meaning1683 q) (meaning1696 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1683 = false ∨ valuation q 1696 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1697)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 5 2 (meaning1663 q) (meaning1684 q) (meaning1697 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1684 = false ∨ valuation q 1697 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1698 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1698)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 5 3 (meaning1663 q) (meaning1685 q) (meaning1698 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1685 = false ∨ valuation q 1698 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_left (literal (valuationOf q) (1664)) (literal (valuationOf q) (1696)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 6 (meaning1664 q) (meaning1696 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1696 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1697)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 6 1 (meaning1664 q) (meaning1683 q) (meaning1697 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1683 = false ∨ valuation q 1697 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1698 = true := by
  have hs : count1691 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) + (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73]) (l₂ := [-75, -76, -78, -80, -83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1698)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73]) (countLit q [-75, -76, -78, -80, -83, -84, -88, -91]) (count1691 q) 6 2 (meaning1664 q) (meaning1684 q) (meaning1698 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1684 = false ∨ valuation q 1698 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E020.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112020
