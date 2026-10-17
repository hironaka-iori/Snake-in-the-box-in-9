import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-36]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1477)) (countLit q [-36]) (countLit q [-39]) (count1477 q) 1 (meaningNeg36 q) (meaning1477 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1477 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 39 = true ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-36]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-39])
  have hm := merge_two (literal (valuationOf q) (-36)) (literal (valuationOf q) (-39)) (literal (valuationOf q) (1478)) (countLit q [-36]) (countLit q [-39]) (count1477 q) 1 1 (meaningNeg36 q) (meaningNeg39 q) (meaning1478 q) hs
  change (! (valuationOf q 36)) = false ∨ (! (valuationOf q 39)) = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 39 = true ∨ valuation q 1478 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1479 = true := by
  have hs : count1479 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1479)) (countLit q [-40]) (countLit q [-41]) (count1479 q) 1 (meaningNeg40 q) (meaning1479 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1479 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-36, -39]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -39]) (l₂ := [-40, -41])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1481)) (countLit q [-36, -39]) (countLit q [-40, -41]) (count1481 q) 1 (meaning1479 q) (meaning1481 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1481 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1481 = true := by
  have hs : count1481 q = (countLit q [-36, -39]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -39]) (l₂ := [-40, -41])
  have hm := merge_left (literal (valuationOf q) (1477)) (literal (valuationOf q) (1481)) (countLit q [-36, -39]) (countLit q [-40, -41]) (count1481 q) 1 (meaning1477 q) (meaning1481 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1481 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-36, -39]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -39]) (l₂ := [-40, -41])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1482)) (countLit q [-36, -39]) (countLit q [-40, -41]) (count1481 q) 1 1 (meaning1477 q) (meaning1479 q) (meaning1482 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1479 = false ∨ valuation q 1482 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-36, -39]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -39]) (l₂ := [-40, -41])
  have hm := merge_left (literal (valuationOf q) (1478)) (literal (valuationOf q) (1482)) (countLit q [-36, -39]) (countLit q [-40, -41]) (count1481 q) 2 (meaning1478 q) (meaning1482 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1482 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1483 = true := by
  have hs : count1481 q = (countLit q [-36, -39]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-36, -39]) (l₂ := [-40, -41])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1483)) (countLit q [-36, -39]) (countLit q [-40, -41]) (count1481 q) 2 1 (meaning1478 q) (meaning1479 q) (meaning1483 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1479 = false ∨ valuation q 1483 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-36, -39, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-36, -39, -40, -41])
  have hm := merge_right (literal (valuationOf q) (1481)) (literal (valuationOf q) (1485)) (countLit q [-31, -34, -35]) (countLit q [-36, -39, -40, -41]) (count1485 q) 1 (meaning1481 q) (meaning1485 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1485 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-36, -39, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-36, -39, -40, -41])
  have hm := merge_right (literal (valuationOf q) (1482)) (literal (valuationOf q) (1486)) (countLit q [-31, -34, -35]) (countLit q [-36, -39, -40, -41]) (count1485 q) 2 (meaning1482 q) (meaning1486 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1486 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-36, -39, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-36, -39, -40, -41])
  have hm := merge_right (literal (valuationOf q) (1483)) (literal (valuationOf q) (1487)) (countLit q [-31, -34, -35]) (countLit q [-36, -39, -40, -41]) (count1485 q) 3 (meaning1483 q) (meaning1487 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1487 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-36, -39, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-36, -39, -40, -41])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1486)) (countLit q [-31, -34, -35]) (countLit q [-36, -39, -40, -41]) (count1485 q) 1 1 (meaning1474 q) (meaning1481 q) (meaning1486 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1481 = false ∨ valuation q 1486 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-36, -39, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-36, -39, -40, -41])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1487)) (countLit q [-31, -34, -35]) (countLit q [-36, -39, -40, -41]) (count1485 q) 1 2 (meaning1474 q) (meaning1482 q) (meaning1487 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1482 = false ∨ valuation q 1487 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-36, -39, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-36, -39, -40, -41])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1488)) (countLit q [-31, -34, -35]) (countLit q [-36, -39, -40, -41]) (count1485 q) 1 3 (meaning1474 q) (meaning1483 q) (meaning1488 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1483 = false ∨ valuation q 1488 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-36, -39, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-36, -39, -40, -41])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1487)) (countLit q [-31, -34, -35]) (countLit q [-36, -39, -40, -41]) (count1485 q) 2 1 (meaning1475 q) (meaning1481 q) (meaning1487 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1481 = false ∨ valuation q 1487 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-36, -39, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-36, -39, -40, -41])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1488)) (countLit q [-31, -34, -35]) (countLit q [-36, -39, -40, -41]) (count1485 q) 2 2 (meaning1475 q) (meaning1482 q) (meaning1488 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1482 = false ∨ valuation q 1488 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-36, -39, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-36, -39, -40, -41])
  have hm := merge_two (literal (valuationOf q) (1476)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1488)) (countLit q [-31, -34, -35]) (countLit q [-36, -39, -40, -41]) (count1485 q) 3 1 (meaning1476 q) (meaning1481 q) (meaning1488 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1481 = false ∨ valuation q 1488 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-36, -39, -40, -41]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-36, -39, -40, -41])
  have hm := merge_two (literal (valuationOf q) (1476)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1489)) (countLit q [-31, -34, -35]) (countLit q [-36, -39, -40, -41]) (count1485 q) 3 2 (meaning1476 q) (meaning1482 q) (meaning1489 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1482 = false ∨ valuation q 1489 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1492)) (countLit q [-44]) (countLit q [-45]) (count1492 q) 1 (meaningNeg45 q) (meaning1492 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1492 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1492)) (countLit q [-44]) (countLit q [-45]) (count1492 q) 1 (meaningNeg44 q) (meaning1492 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1492 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 45 = true ∨ valuationOf q 1493 = true := by
  have hs : count1492 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (1493)) (countLit q [-44]) (countLit q [-45]) (count1492 q) 1 1 (meaningNeg44 q) (meaningNeg45 q) (meaning1493 q) hs
  change (! (valuationOf q 44)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 45 = true ∨ valuation q 1493 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1494)) (countLit q [-48]) (countLit q [-49]) (count1494 q) 1 (meaningNeg49 q) (meaning1494 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1494 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1494)) (countLit q [-48]) (countLit q [-49]) (count1494 q) 1 (meaningNeg48 q) (meaning1494 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1494 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-44, -45]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-48, -49])
  have hm := merge_right (literal (valuationOf q) (1494)) (literal (valuationOf q) (1496)) (countLit q [-44, -45]) (countLit q [-48, -49]) (count1496 q) 1 (meaning1494 q) (meaning1496 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1496 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-44, -45]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-48, -49])
  have hm := merge_left (literal (valuationOf q) (1492)) (literal (valuationOf q) (1496)) (countLit q [-44, -45]) (countLit q [-48, -49]) (count1496 q) 1 (meaning1492 q) (meaning1496 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1496 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-44, -45]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-48, -49])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1497)) (countLit q [-44, -45]) (countLit q [-48, -49]) (count1496 q) 1 1 (meaning1492 q) (meaning1494 q) (meaning1497 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1494 = false ∨ valuation q 1497 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-44, -45]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-48, -49])
  have hm := merge_left (literal (valuationOf q) (1493)) (literal (valuationOf q) (1497)) (countLit q [-44, -45]) (countLit q [-48, -49]) (count1496 q) 2 (meaning1493 q) (meaning1497 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1497 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1498 = true := by
  have hs : count1496 q = (countLit q [-44, -45]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-44, -45]) (l₂ := [-48, -49])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1498)) (countLit q [-44, -45]) (countLit q [-48, -49]) (count1496 q) 2 1 (meaning1493 q) (meaning1494 q) (meaning1498 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1494 = false ∨ valuation q 1498 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-50]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1500)) (countLit q [-50]) (countLit q [-52]) (count1500 q) 1 (meaningNeg52 q) (meaning1500 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1500 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1502)) (countLit q [-55]) (countLit q [-56]) (count1502 q) 1 (meaningNeg55 q) (meaning1502 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1502 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-50, -52]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -52]) (l₂ := [-55, -56])
  have hm := merge_left (literal (valuationOf q) (1500)) (literal (valuationOf q) (1504)) (countLit q [-50, -52]) (countLit q [-55, -56]) (count1504 q) 1 (meaning1500 q) (meaning1504 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1504 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true := by
  have hs : count1504 q = (countLit q [-50, -52]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -52]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1505)) (countLit q [-50, -52]) (countLit q [-55, -56]) (count1504 q) 1 1 (meaning1500 q) (meaning1502 q) (meaning1505 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1502 = false ∨ valuation q 1505 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E104.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112104
