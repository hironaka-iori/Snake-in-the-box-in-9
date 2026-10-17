import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1472 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1472)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 2 3 (meaning1458 q) (meaning1466 q) (meaning1472 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1466 = false ∨ valuation q 1472 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1473 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1473)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 2 4 (meaning1458 q) (meaning1467 q) (meaning1473 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1467 = false ∨ valuation q 1473 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1470 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_left (literal (valuationOf q) (1459)) (literal (valuationOf q) (1470)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 3 (meaning1459 q) (meaning1470 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1470 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1471 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1471)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 3 1 (meaning1459 q) (meaning1464 q) (meaning1471 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1464 = false ∨ valuation q 1471 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1472 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1472)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 3 2 (meaning1459 q) (meaning1465 q) (meaning1472 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1465 = false ∨ valuation q 1472 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1473 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1473)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 3 3 (meaning1459 q) (meaning1466 q) (meaning1473 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1466 = false ∨ valuation q 1473 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1474 = true := by
  have hs : count1468 q = (countLit q [-30, -31, -35]) + (countLit q [-36, -38, -40, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35]) (l₂ := [-36, -38, -40, -42])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1474)) (countLit q [-30, -31, -35]) (countLit q [-36, -38, -40, -42]) (count1468 q) 3 4 (meaning1459 q) (meaning1467 q) (meaning1474 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1467 = false ∨ valuation q 1474 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (1475)) (countLit q [-45]) (countLit q [-46]) (count1475 q) 1 (meaningNeg46 q) (meaning1475 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1475 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (1475)) (countLit q [-45]) (countLit q [-46]) (count1475 q) 1 (meaningNeg45 q) (meaning1475 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1475 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 46 = true ∨ valuationOf q 1476 = true := by
  have hs : count1475 q = (countLit q [-45]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-45)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (1476)) (countLit q [-45]) (countLit q [-46]) (count1475 q) 1 1 (meaningNeg45 q) (meaningNeg46 q) (meaning1476 q) hs
  change (! (valuationOf q 45)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 46 = true ∨ valuation q 1476 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_right (literal (valuationOf q) (1475)) (literal (valuationOf q) (1477)) (countLit q [-43]) (countLit q [-45, -46]) (count1477 q) 1 (meaning1475 q) (meaning1477 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1477 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1478)) (countLit q [-43]) (countLit q [-45, -46]) (count1477 q) 2 (meaning1476 q) (meaning1478 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1478 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (1477)) (countLit q [-43]) (countLit q [-45, -46]) (count1477 q) 1 (meaningNeg43 q) (meaning1477 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1477 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1478)) (countLit q [-43]) (countLit q [-45, -46]) (count1477 q) 1 1 (meaningNeg43 q) (meaning1475 q) (meaning1478 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1475 = false ∨ valuation q 1478 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-43]) + (countLit q [-45, -46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-45, -46])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1479)) (countLit q [-43]) (countLit q [-45, -46]) (count1477 q) 1 2 (meaningNeg43 q) (meaning1476 q) (meaning1479 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1476 = false ∨ valuation q 1479 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1480)) (countLit q [-49]) (countLit q [-51]) (count1480 q) 1 (meaningNeg51 q) (meaning1480 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1480 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (1480)) (countLit q [-49]) (countLit q [-51]) (count1480 q) 1 (meaningNeg49 q) (meaning1480 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1480 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1481 = true := by
  have hs : count1480 q = (countLit q [-49]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1481)) (countLit q [-49]) (countLit q [-51]) (count1480 q) 1 1 (meaningNeg49 q) (meaningNeg51 q) (meaning1481 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 51 = true ∨ valuation q 1481 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-52]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (1482)) (countLit q [-52]) (countLit q [-55]) (count1482 q) 1 (meaningNeg55 q) (meaning1482 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1482 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-52]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1482)) (countLit q [-52]) (countLit q [-55]) (count1482 q) 1 (meaningNeg52 q) (meaning1482 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1482 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 55 = true ∨ valuationOf q 1483 = true := by
  have hs : count1482 q = (countLit q [-52]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (1483)) (countLit q [-52]) (countLit q [-55]) (count1482 q) 1 1 (meaningNeg52 q) (meaningNeg55 q) (meaning1483 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 55 = true ∨ valuation q 1483 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1484 = true := by
  have hs : count1484 q = (countLit q [-49, -51]) + (countLit q [-52, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-52, -55])
  have hm := merge_right (literal (valuationOf q) (1482)) (literal (valuationOf q) (1484)) (countLit q [-49, -51]) (countLit q [-52, -55]) (count1484 q) 1 (meaning1482 q) (meaning1484 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1484 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-49, -51]) + (countLit q [-52, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-52, -55])
  have hm := merge_right (literal (valuationOf q) (1483)) (literal (valuationOf q) (1485)) (countLit q [-49, -51]) (countLit q [-52, -55]) (count1484 q) 2 (meaning1483 q) (meaning1485 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1485 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1484 = true := by
  have hs : count1484 q = (countLit q [-49, -51]) + (countLit q [-52, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-52, -55])
  have hm := merge_left (literal (valuationOf q) (1480)) (literal (valuationOf q) (1484)) (countLit q [-49, -51]) (countLit q [-52, -55]) (count1484 q) 1 (meaning1480 q) (meaning1484 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1484 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-49, -51]) + (countLit q [-52, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-52, -55])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1485)) (countLit q [-49, -51]) (countLit q [-52, -55]) (count1484 q) 1 1 (meaning1480 q) (meaning1482 q) (meaning1485 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1482 = false ∨ valuation q 1485 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-49, -51]) + (countLit q [-52, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-52, -55])
  have hm := merge_left (literal (valuationOf q) (1481)) (literal (valuationOf q) (1485)) (countLit q [-49, -51]) (countLit q [-52, -55]) (count1484 q) 2 (meaning1481 q) (meaning1485 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1485 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1486 = true := by
  have hs : count1484 q = (countLit q [-49, -51]) + (countLit q [-52, -55]) := List.countP_append (p := literal q) (l₁ := [-49, -51]) (l₂ := [-52, -55])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1486)) (countLit q [-49, -51]) (countLit q [-52, -55]) (count1484 q) 2 1 (meaning1481 q) (meaning1482 q) (meaning1486 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1482 = false ∨ valuation q 1486 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_right (literal (valuationOf q) (1484)) (literal (valuationOf q) (1488)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 1 (meaning1484 q) (meaning1488 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1488 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_right (literal (valuationOf q) (1485)) (literal (valuationOf q) (1489)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 2 (meaning1485 q) (meaning1489 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1489 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_right (literal (valuationOf q) (1486)) (literal (valuationOf q) (1490)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 3 (meaning1486 q) (meaning1490 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1490 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_left (literal (valuationOf q) (1477)) (literal (valuationOf q) (1488)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 1 (meaning1477 q) (meaning1488 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1488 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1489)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 1 1 (meaning1477 q) (meaning1484 q) (meaning1489 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1484 = false ∨ valuation q 1489 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E169.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112169
