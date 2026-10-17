import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-6, -8]) + (countLit q [-10, -11]) := List.countP_append (p := literal q) (l₁ := [-6, -8]) (l₂ := [-10, -11])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1455)) (countLit q [-6, -8]) (countLit q [-10, -11]) (count1452 q) 2 2 (meaning1449 q) (meaning1451 q) (meaning1455 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1451 = false ∨ valuation q 1455 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_right (literal (valuationOf q) (1452)) (literal (valuationOf q) (1456)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 1 (meaning1452 q) (meaning1456 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1456 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_right (literal (valuationOf q) (1453)) (literal (valuationOf q) (1457)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 2 (meaning1453 q) (meaning1457 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1457 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1458 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_right (literal (valuationOf q) (1454)) (literal (valuationOf q) (1458)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 3 (meaning1454 q) (meaning1458 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1458 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1459 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_right (literal (valuationOf q) (1455)) (literal (valuationOf q) (1459)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 4 (meaning1455 q) (meaning1459 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1459 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1456 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_left (literal (valuationOf q) (1445)) (literal (valuationOf q) (1456)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 1 (meaning1445 q) (meaning1456 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1456 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1457)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 1 1 (meaning1445 q) (meaning1452 q) (meaning1457 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1452 = false ∨ valuation q 1457 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1458 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1458)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 1 2 (meaning1445 q) (meaning1453 q) (meaning1458 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1453 = false ∨ valuation q 1458 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1459 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1459)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 1 3 (meaning1445 q) (meaning1454 q) (meaning1459 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1454 = false ∨ valuation q 1459 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1460 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1460)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 1 4 (meaning1445 q) (meaning1455 q) (meaning1460 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1455 = false ∨ valuation q 1460 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1457 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_left (literal (valuationOf q) (1446)) (literal (valuationOf q) (1457)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 2 (meaning1446 q) (meaning1457 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1457 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1458 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1458)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 2 1 (meaning1446 q) (meaning1452 q) (meaning1458 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1452 = false ∨ valuation q 1458 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1459 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1459)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 2 2 (meaning1446 q) (meaning1453 q) (meaning1459 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1453 = false ∨ valuation q 1459 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1460 = true := by
  have hs : count1456 q = (countLit q [-1, -3, -5]) + (countLit q [-6, -8, -10, -11]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5]) (l₂ := [-6, -8, -10, -11])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1460)) (countLit q [-1, -3, -5]) (countLit q [-6, -8, -10, -11]) (count1456 q) 2 3 (meaning1446 q) (meaning1454 q) (meaning1460 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1454 = false ∨ valuation q 1460 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_right (literal (valuationOf q) (-14)) (literal (valuationOf q) (1463)) (countLit q [-13]) (countLit q [-14]) (count1463 q) 1 (meaningNeg14 q) (meaning1463 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1463 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1463)) (countLit q [-13]) (countLit q [-14]) (count1463 q) 1 (meaningNeg13 q) (meaning1463 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1463 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 14 = true ∨ valuationOf q 1464 = true := by
  have hs : count1463 q = (countLit q [-13]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-14])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-14)) (literal (valuationOf q) (1464)) (countLit q [-13]) (countLit q [-14]) (count1463 q) 1 1 (meaningNeg13 q) (meaningNeg14 q) (meaning1464 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 14)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 14 = true ∨ valuation q 1464 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1465)) (countLit q [-18]) (countLit q [-19]) (count1465 q) 1 (meaningNeg19 q) (meaning1465 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1465 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1465)) (countLit q [-18]) (countLit q [-19]) (count1465 q) 1 (meaningNeg18 q) (meaning1465 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1465 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 19 = true ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (1466)) (countLit q [-18]) (countLit q [-19]) (count1465 q) 1 1 (meaningNeg18 q) (meaningNeg19 q) (meaning1466 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 1466 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_right (literal (valuationOf q) (1465)) (literal (valuationOf q) (1467)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 1 (meaning1465 q) (meaning1467 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1467 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_right (literal (valuationOf q) (1466)) (literal (valuationOf q) (1468)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 2 (meaning1466 q) (meaning1468 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1468 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_left (literal (valuationOf q) (1463)) (literal (valuationOf q) (1467)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 1 (meaning1463 q) (meaning1467 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1467 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1468)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 1 1 (meaning1463 q) (meaning1465 q) (meaning1468 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1465 = false ∨ valuation q 1468 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1469 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1469)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 1 2 (meaning1463 q) (meaning1466 q) (meaning1469 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1466 = false ∨ valuation q 1469 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_left (literal (valuationOf q) (1464)) (literal (valuationOf q) (1468)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 2 (meaning1464 q) (meaning1468 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1468 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1469 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1469)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 2 1 (meaning1464 q) (meaning1465 q) (meaning1469 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1465 = false ∨ valuation q 1469 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1470 = true := by
  have hs : count1467 q = (countLit q [-13, -14]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -14]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (1464)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1470)) (countLit q [-13, -14]) (countLit q [-18, -19]) (count1467 q) 2 2 (meaning1464 q) (meaning1466 q) (meaning1470 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1466 = false ∨ valuation q 1470 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1471)) (countLit q [-20]) (countLit q [-22]) (count1471 q) 1 (meaningNeg22 q) (meaning1471 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1471 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1471)) (countLit q [-20]) (countLit q [-22]) (count1471 q) 1 (meaningNeg20 q) (meaning1471 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1471 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1472 = true := by
  have hs : count1471 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1472)) (countLit q [-20]) (countLit q [-22]) (count1471 q) 1 1 (meaningNeg20 q) (meaningNeg22 q) (meaning1472 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 1472 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1473 = true := by
  have hs : count1473 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1473)) (countLit q [-25]) (countLit q [-26]) (count1473 q) 1 (meaningNeg26 q) (meaning1473 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1473 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E024.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112024
