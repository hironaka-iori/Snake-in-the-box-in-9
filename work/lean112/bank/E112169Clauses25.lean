import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1455 = true := by
  have hs : count1455 q = (countLit q [-31]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1455)) (countLit q [-31]) (countLit q [-35]) (count1455 q) 1 (meaningNeg31 q) (meaning1455 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1455 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1456 = true := by
  have hs : count1455 q = (countLit q [-31]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1456)) (countLit q [-31]) (countLit q [-35]) (count1455 q) 1 1 (meaningNeg31 q) (meaningNeg35 q) (meaning1456 q) hs
  change (! (valuationOf q 31)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 35 = true ∨ valuation q 1456 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-30]) + (countLit q [-31, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -35])
  have hm := merge_right (literal (valuationOf q) (1455)) (literal (valuationOf q) (1457)) (countLit q [-30]) (countLit q [-31, -35]) (count1457 q) 1 (meaning1455 q) (meaning1457 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1457 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1458 = true := by
  have hs : count1457 q = (countLit q [-30]) + (countLit q [-31, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -35])
  have hm := merge_right (literal (valuationOf q) (1456)) (literal (valuationOf q) (1458)) (countLit q [-30]) (countLit q [-31, -35]) (count1457 q) 2 (meaning1456 q) (meaning1458 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1458 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-30]) + (countLit q [-31, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -35])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1457)) (countLit q [-30]) (countLit q [-31, -35]) (count1457 q) 1 (meaningNeg30 q) (meaning1457 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1457 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1455 = false ∨ valuationOf q 1458 = true := by
  have hs : count1457 q = (countLit q [-30]) + (countLit q [-31, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -35])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1458)) (countLit q [-30]) (countLit q [-31, -35]) (count1457 q) 1 1 (meaningNeg30 q) (meaning1455 q) (meaning1458 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1455 = false ∨ valuation q 1458 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1456 = false ∨ valuationOf q 1459 = true := by
  have hs : count1457 q = (countLit q [-30]) + (countLit q [-31, -35]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -35])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1459)) (countLit q [-30]) (countLit q [-31, -35]) (count1457 q) 1 2 (meaningNeg30 q) (meaning1456 q) (meaning1459 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1456 = false ∨ valuation q 1459 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1460 = true := by
  have hs : count1460 q = (countLit q [-36]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (1460)) (countLit q [-36]) (countLit q [-38]) (count1460 q) 1 (meaningNeg38 q) (meaning1460 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1460 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1460 = true := by
  have hs : count1460 q = (countLit q [-36]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1460)) (countLit q [-36]) (countLit q [-38]) (count1460 q) 1 (meaningNeg36 q) (meaning1460 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1460 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 38 = true ∨ valuationOf q 1461 = true := by
  have hs : count1460 q = (countLit q [-36]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-36)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (1461)) (countLit q [-36]) (countLit q [-38]) (count1460 q) 1 1 (meaningNeg36 q) (meaningNeg38 q) (meaning1461 q) hs
  change (! (valuationOf q 36)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 38 = true ∨ valuation q 1461 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1462)) (countLit q [-40]) (countLit q [-42]) (count1462 q) 1 (meaningNeg42 q) (meaning1462 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1462 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1462)) (countLit q [-40]) (countLit q [-42]) (count1462 q) 1 (meaningNeg40 q) (meaning1462 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1462 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1463 = true := by
  have hs : count1462 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1463)) (countLit q [-40]) (countLit q [-42]) (count1462 q) 1 1 (meaningNeg40 q) (meaningNeg42 q) (meaning1463 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 1463 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-36, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -38]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1462)) (literal (valuationOf q) (1464)) (countLit q [-36, -38]) (countLit q [-40, -42]) (count1464 q) 1 (meaning1462 q) (meaning1464 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1464 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1465 = true := by
  have hs : count1464 q = (countLit q [-36, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -38]) (l₂ := [-40, -42])
  have hm := merge_right (literal (valuationOf q) (1463)) (literal (valuationOf q) (1465)) (countLit q [-36, -38]) (countLit q [-40, -42]) (count1464 q) 2 (meaning1463 q) (meaning1465 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1465 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-36, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -38]) (l₂ := [-40, -42])
  have hm := merge_left (literal (valuationOf q) (1460)) (literal (valuationOf q) (1464)) (countLit q [-36, -38]) (countLit q [-40, -42]) (count1464 q) 1 (meaning1460 q) (meaning1464 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1464 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1465 = true := by
  have hs : count1464 q = (countLit q [-36, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -38]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1465)) (countLit q [-36, -38]) (countLit q [-40, -42]) (count1464 q) 1 1 (meaning1460 q) (meaning1462 q) (meaning1465 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1462 = false ∨ valuation q 1465 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true := by
  have hs : count1464 q = (countLit q [-36, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -38]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1466)) (countLit q [-36, -38]) (countLit q [-40, -42]) (count1464 q) 1 2 (meaning1460 q) (meaning1463 q) (meaning1466 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1463 = false ∨ valuation q 1466 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1465 = true := by
  have hs : count1464 q = (countLit q [-36, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -38]) (l₂ := [-40, -42])
  have hm := merge_left (literal (valuationOf q) (1461)) (literal (valuationOf q) (1465)) (countLit q [-36, -38]) (countLit q [-40, -42]) (count1464 q) 2 (meaning1461 q) (meaning1465 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1465 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1466 = true := by
  have hs : count1464 q = (countLit q [-36, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -38]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1466)) (countLit q [-36, -38]) (countLit q [-40, -42]) (count1464 q) 2 1 (meaning1461 q) (meaning1462 q) (meaning1466 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1462 = false ∨ valuation q 1466 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1467 = true := by
  have hs : count1464 q = (countLit q [-36, -38]) + (countLit q [-40, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -38]) (l₂ := [-40, -42])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1467)) (countLit q [-36, -38]) (countLit q [-40, -42]) (count1464 q) 2 2 (meaning1461 q) (meaning1463 q) (meaning1467 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1463 = false ∨ valuation q 1467 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1468 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1468)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 1 (meaning1464 q) (meaning1468 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1468 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1469 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1465)) (literal (valuationOf q) (1469)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 2 (meaning1465 q) (meaning1469 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1469 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1470 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_right (literal (valuationOf q) (1466)) (literal (valuationOf q) (1470)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 3 (meaning1466 q) (meaning1470 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1470 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1468 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1457)) (literal (valuationOf q) (1468)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 1 (meaning1457 q) (meaning1468 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1468 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1469 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1469)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 1 1 (meaning1457 q) (meaning1464 q) (meaning1469 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1464 = false ∨ valuation q 1469 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1470 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1470)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 1 2 (meaning1457 q) (meaning1465 q) (meaning1470 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1465 = false ∨ valuation q 1470 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1471)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 1 3 (meaning1457 q) (meaning1466 q) (meaning1471 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1466 = false ∨ valuation q 1471 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1472 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1472)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 1 4 (meaning1457 q) (meaning1467 q) (meaning1472 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1467 = false ∨ valuation q 1472 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1469 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1458)) (literal (valuationOf q) (1469)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 2 (meaning1458 q) (meaning1469 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1469 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1470 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1470)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 2 1 (meaning1458 q) (meaning1464 q) (meaning1470 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1464 = false ∨ valuation q 1470 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1471 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1471)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 2 2 (meaning1458 q) (meaning1465 q) (meaning1471 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1465 = false ∨ valuation q 1471 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E169.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112169
