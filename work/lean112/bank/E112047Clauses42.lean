import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-92]) + (countLit q [-93, -96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -96])
  have hm := merge_right (literal (valuationOf q) (1624)) (literal (valuationOf q) (1626)) (countLit q [-92]) (countLit q [-93, -96]) (count1625 q) 2 (meaning1624 q) (meaning1626 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1626 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-92]) + (countLit q [-93, -96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -96])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1625)) (countLit q [-92]) (countLit q [-93, -96]) (count1625 q) 1 (meaningNeg92 q) (meaning1625 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1625 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1623 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-92]) + (countLit q [-93, -96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -96])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1626)) (countLit q [-92]) (countLit q [-93, -96]) (count1625 q) 1 1 (meaningNeg92 q) (meaning1623 q) (meaning1626 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1623 = false ∨ valuation q 1626 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1624 = false ∨ valuationOf q 1627 = true := by
  have hs : count1625 q = (countLit q [-92]) + (countLit q [-93, -96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -96])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1627)) (countLit q [-92]) (countLit q [-93, -96]) (count1625 q) 1 2 (meaningNeg92 q) (meaning1624 q) (meaning1627 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1624 = false ∨ valuation q 1627 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1628 = true := by
  have hs : count1628 q = (countLit q [-97]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1628)) (countLit q [-97]) (countLit q [-101]) (count1628 q) 1 (meaningNeg101 q) (meaning1628 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1628 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1628 = true := by
  have hs : count1628 q = (countLit q [-97]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-101])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1628)) (countLit q [-97]) (countLit q [-101]) (count1628 q) 1 (meaningNeg97 q) (meaning1628 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1628 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 101 = true ∨ valuationOf q 1629 = true := by
  have hs : count1628 q = (countLit q [-97]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-101])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-101)) (literal (valuationOf q) (1629)) (countLit q [-97]) (countLit q [-101]) (count1628 q) 1 1 (meaningNeg97 q) (meaningNeg101 q) (meaning1629 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 101)) = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 101 = true ∨ valuation q 1629 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1630)) (countLit q [-103]) (countLit q [-104]) (count1630 q) 1 (meaningNeg104 q) (meaning1630 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1630 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1630 = true := by
  have hs : count1630 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1630)) (countLit q [-103]) (countLit q [-104]) (count1630 q) 1 (meaningNeg103 q) (meaning1630 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1630 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 104 = true ∨ valuationOf q 1631 = true := by
  have hs : count1630 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-104)) (literal (valuationOf q) (1631)) (countLit q [-103]) (countLit q [-104]) (count1630 q) 1 1 (meaningNeg103 q) (meaningNeg104 q) (meaning1631 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 104)) = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 104 = true ∨ valuation q 1631 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-97, -101]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -101]) (l₂ := [-103, -104])
  have hm := merge_right (literal (valuationOf q) (1630)) (literal (valuationOf q) (1632)) (countLit q [-97, -101]) (countLit q [-103, -104]) (count1632 q) 1 (meaning1630 q) (meaning1632 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1632 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-97, -101]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -101]) (l₂ := [-103, -104])
  have hm := merge_right (literal (valuationOf q) (1631)) (literal (valuationOf q) (1633)) (countLit q [-97, -101]) (countLit q [-103, -104]) (count1632 q) 2 (meaning1631 q) (meaning1633 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1633 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-97, -101]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -101]) (l₂ := [-103, -104])
  have hm := merge_left (literal (valuationOf q) (1628)) (literal (valuationOf q) (1632)) (countLit q [-97, -101]) (countLit q [-103, -104]) (count1632 q) 1 (meaning1628 q) (meaning1632 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1632 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-97, -101]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -101]) (l₂ := [-103, -104])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1633)) (countLit q [-97, -101]) (countLit q [-103, -104]) (count1632 q) 1 1 (meaning1628 q) (meaning1630 q) (meaning1633 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1630 = false ∨ valuation q 1633 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1634 = true := by
  have hs : count1632 q = (countLit q [-97, -101]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -101]) (l₂ := [-103, -104])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1634)) (countLit q [-97, -101]) (countLit q [-103, -104]) (count1632 q) 1 2 (meaning1628 q) (meaning1631 q) (meaning1634 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1631 = false ∨ valuation q 1634 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-97, -101]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -101]) (l₂ := [-103, -104])
  have hm := merge_left (literal (valuationOf q) (1629)) (literal (valuationOf q) (1633)) (countLit q [-97, -101]) (countLit q [-103, -104]) (count1632 q) 2 (meaning1629 q) (meaning1633 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1633 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1634 = true := by
  have hs : count1632 q = (countLit q [-97, -101]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -101]) (l₂ := [-103, -104])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1634)) (countLit q [-97, -101]) (countLit q [-103, -104]) (count1632 q) 2 1 (meaning1629 q) (meaning1630 q) (meaning1634 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1630 = false ∨ valuation q 1634 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1635 = true := by
  have hs : count1632 q = (countLit q [-97, -101]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-97, -101]) (l₂ := [-103, -104])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1635)) (countLit q [-97, -101]) (countLit q [-103, -104]) (count1632 q) 2 2 (meaning1629 q) (meaning1631 q) (meaning1635 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1631 = false ∨ valuation q 1635 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1636 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_right (literal (valuationOf q) (1632)) (literal (valuationOf q) (1636)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 1 (meaning1632 q) (meaning1636 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1636 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1637 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1637)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 2 (meaning1633 q) (meaning1637 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1637 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1638 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_right (literal (valuationOf q) (1634)) (literal (valuationOf q) (1638)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 3 (meaning1634 q) (meaning1638 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1638 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1636 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_left (literal (valuationOf q) (1625)) (literal (valuationOf q) (1636)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 1 (meaning1625 q) (meaning1636 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1636 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1637 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1637)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 1 1 (meaning1625 q) (meaning1632 q) (meaning1637 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1632 = false ∨ valuation q 1637 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1638 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1638)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 1 2 (meaning1625 q) (meaning1633 q) (meaning1638 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1633 = false ∨ valuation q 1638 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1639 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1639)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 1 3 (meaning1625 q) (meaning1634 q) (meaning1639 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1634 = false ∨ valuation q 1639 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1635 = false ∨ valuationOf q 1640 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1635)) (literal (valuationOf q) (1640)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 1 4 (meaning1625 q) (meaning1635 q) (meaning1640 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1635 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1635 = false ∨ valuation q 1640 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1637 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_left (literal (valuationOf q) (1626)) (literal (valuationOf q) (1637)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 2 (meaning1626 q) (meaning1637 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1637 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1638 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1638)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 2 1 (meaning1626 q) (meaning1632 q) (meaning1638 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1632 = false ∨ valuation q 1638 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1639 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1633)) (literal (valuationOf q) (1639)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 2 2 (meaning1626 q) (meaning1633 q) (meaning1639 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1633 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1633 = false ∨ valuation q 1639 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1640 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1634)) (literal (valuationOf q) (1640)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 2 3 (meaning1626 q) (meaning1634 q) (meaning1640 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1634 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1634 = false ∨ valuation q 1640 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1635 = false ∨ valuationOf q 1641 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1635)) (literal (valuationOf q) (1641)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 2 4 (meaning1626 q) (meaning1635 q) (meaning1641 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1635 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1635 = false ∨ valuation q 1641 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1638 = true := by
  have hs : count1636 q = (countLit q [-92, -93, -96]) + (countLit q [-97, -101, -103, -104]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -96]) (l₂ := [-97, -101, -103, -104])
  have hm := merge_left (literal (valuationOf q) (1627)) (literal (valuationOf q) (1638)) (countLit q [-92, -93, -96]) (countLit q [-97, -101, -103, -104]) (count1636 q) 3 (meaning1627 q) (meaning1638 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1638 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E047.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112047
