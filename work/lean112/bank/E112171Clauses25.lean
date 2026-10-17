import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1462 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1455)) (literal (valuationOf q) (1462)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 4 (meaning1455 q) (meaning1462 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1462 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1460)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 1 1 (meaning1432 q) (meaning1452 q) (meaning1460 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1452 = false ∨ valuation q 1460 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1461 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1461)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 1 2 (meaning1432 q) (meaning1453 q) (meaning1461 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1453 = false ∨ valuation q 1461 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1462 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1462)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 1 3 (meaning1432 q) (meaning1454 q) (meaning1462 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1454 = false ∨ valuation q 1462 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1463 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1463)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 1 4 (meaning1432 q) (meaning1455 q) (meaning1463 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1455 = false ∨ valuation q 1463 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1464 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1464)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 1 5 (meaning1432 q) (meaning1456 q) (meaning1464 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1456 = false ∨ valuation q 1464 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1465 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1465)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 1 6 (meaning1432 q) (meaning1457 q) (meaning1465 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1457 = false ∨ valuation q 1465 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1466 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1466)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 1 7 (meaning1432 q) (meaning1458 q) (meaning1466 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1458 = false ∨ valuation q 1466 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1461 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1461)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 2 1 (meaning1433 q) (meaning1452 q) (meaning1461 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1452 = false ∨ valuation q 1461 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1462 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1462)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 2 2 (meaning1433 q) (meaning1453 q) (meaning1462 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1453 = false ∨ valuation q 1462 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1463 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1463)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 2 3 (meaning1433 q) (meaning1454 q) (meaning1463 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1454 = false ∨ valuation q 1463 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1464 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1464)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 2 4 (meaning1433 q) (meaning1455 q) (meaning1464 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1455 = false ∨ valuation q 1464 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1465 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1465)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 2 5 (meaning1433 q) (meaning1456 q) (meaning1465 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1456 = false ∨ valuation q 1465 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1466 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1466)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 2 6 (meaning1433 q) (meaning1457 q) (meaning1466 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1457 = false ∨ valuation q 1466 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1461 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1434)) (literal (valuationOf q) (1461)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 3 (meaning1434 q) (meaning1461 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1461 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1462 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1462)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 3 1 (meaning1434 q) (meaning1452 q) (meaning1462 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1452 = false ∨ valuation q 1462 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1463 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1463)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 3 2 (meaning1434 q) (meaning1453 q) (meaning1463 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1453 = false ∨ valuation q 1463 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1464 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1464)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 3 3 (meaning1434 q) (meaning1454 q) (meaning1464 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1454 = false ∨ valuation q 1464 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1465 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1465)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 3 4 (meaning1434 q) (meaning1455 q) (meaning1465 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1455 = false ∨ valuation q 1465 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1466 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1466)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 3 5 (meaning1434 q) (meaning1456 q) (meaning1466 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1456 = false ∨ valuation q 1466 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1467 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1467)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 3 6 (meaning1434 q) (meaning1457 q) (meaning1467 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1457 = false ∨ valuation q 1467 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1464 = true := by
  have hs : count1459 q = (countLit q [-30, -32, -34, -35, -36, -40, -42]) + (countLit q [-44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34, -35, -36, -40, -42]) (l₂ := [-44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1464)) (countLit q [-30, -32, -34, -35, -36, -40, -42]) (countLit q [-44, -48, -49, -52, -54, -56, -57]) (count1459 q) 4 2 (meaning1435 q) (meaning1453 q) (meaning1464 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1453 = false ∨ valuation q 1464 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1479 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1479)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 2 5 (meaning1406 q) (meaning1463 q) (meaning1479 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1463 = false ∨ valuation q 1479 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1480 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1480)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 2 6 (meaning1406 q) (meaning1464 q) (meaning1480 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1464 = false ∨ valuation q 1480 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1481 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1481)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 2 7 (meaning1406 q) (meaning1465 q) (meaning1481 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1465 = false ∨ valuation q 1481 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1482 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1482)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 2 8 (meaning1406 q) (meaning1466 q) (meaning1482 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1466 = false ∨ valuation q 1482 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1483 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1483)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 2 9 (meaning1406 q) (meaning1467 q) (meaning1483 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1467 = false ∨ valuation q 1483 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1478 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1461)) (literal (valuationOf q) (1478)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 3 3 (meaning1407 q) (meaning1461 q) (meaning1478 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1461 = false ∨ valuation q 1478 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1479 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1479)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 3 4 (meaning1407 q) (meaning1462 q) (meaning1479 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1462 = false ∨ valuation q 1479 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1480 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1480)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 3 5 (meaning1407 q) (meaning1463 q) (meaning1480 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1463 = false ∨ valuation q 1480 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1481 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1481)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 3 6 (meaning1407 q) (meaning1464 q) (meaning1481 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1464 = false ∨ valuation q 1481 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1482 = true := by
  have hs : count1473 q = (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) + (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (l₂ := [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1482)) (countLit q [-2, -4, -5, -8, -9, -11, -14, -17, -18, -19, -21, -23, -26, -27]) (countLit q [-30, -32, -34, -35, -36, -40, -42, -44, -48, -49, -52, -54, -56, -57]) (count1473 q) 3 7 (meaning1407 q) (meaning1465 q) (meaning1482 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1465 = false ∨ valuation q 1482 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E171.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112171
