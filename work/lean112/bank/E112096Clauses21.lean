import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1483 = true := by
  have hs : count1481 q = (countLit q [-37, -39]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -39]) (l₂ := [-41, -43])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1483)) (countLit q [-37, -39]) (countLit q [-41, -43]) (count1481 q) 1 2 (meaning1477 q) (meaning1480 q) (meaning1483 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1480 = false ∨ valuation q 1483 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1482 = true := by
  have hs : count1481 q = (countLit q [-37, -39]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -39]) (l₂ := [-41, -43])
  have hm := merge_left (literal (valuationOf q) (1478)) (literal (valuationOf q) (1482)) (countLit q [-37, -39]) (countLit q [-41, -43]) (count1481 q) 2 (meaning1478 q) (meaning1482 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1482 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1483 = true := by
  have hs : count1481 q = (countLit q [-37, -39]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-37, -39]) (l₂ := [-41, -43])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1483)) (countLit q [-37, -39]) (countLit q [-41, -43]) (count1481 q) 2 1 (meaning1478 q) (meaning1479 q) (meaning1483 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1479 = false ∨ valuation q 1483 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-37, -39, -41, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-37, -39, -41, -43])
  have hm := merge_right (literal (valuationOf q) (1481)) (literal (valuationOf q) (1485)) (countLit q [-31, -34, -35]) (countLit q [-37, -39, -41, -43]) (count1485 q) 1 (meaning1481 q) (meaning1485 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1485 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-37, -39, -41, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-37, -39, -41, -43])
  have hm := merge_right (literal (valuationOf q) (1482)) (literal (valuationOf q) (1486)) (countLit q [-31, -34, -35]) (countLit q [-37, -39, -41, -43]) (count1485 q) 2 (meaning1482 q) (meaning1486 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1486 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-37, -39, -41, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-37, -39, -41, -43])
  have hm := merge_right (literal (valuationOf q) (1483)) (literal (valuationOf q) (1487)) (countLit q [-31, -34, -35]) (countLit q [-37, -39, -41, -43]) (count1485 q) 3 (meaning1483 q) (meaning1487 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1487 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-37, -39, -41, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-37, -39, -41, -43])
  have hm := merge_left (literal (valuationOf q) (1474)) (literal (valuationOf q) (1485)) (countLit q [-31, -34, -35]) (countLit q [-37, -39, -41, -43]) (count1485 q) 1 (meaning1474 q) (meaning1485 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1485 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-37, -39, -41, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-37, -39, -41, -43])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1486)) (countLit q [-31, -34, -35]) (countLit q [-37, -39, -41, -43]) (count1485 q) 1 1 (meaning1474 q) (meaning1481 q) (meaning1486 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1481 = false ∨ valuation q 1486 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-37, -39, -41, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-37, -39, -41, -43])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1487)) (countLit q [-31, -34, -35]) (countLit q [-37, -39, -41, -43]) (count1485 q) 1 2 (meaning1474 q) (meaning1482 q) (meaning1487 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1482 = false ∨ valuation q 1487 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-37, -39, -41, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-37, -39, -41, -43])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1488)) (countLit q [-31, -34, -35]) (countLit q [-37, -39, -41, -43]) (count1485 q) 1 3 (meaning1474 q) (meaning1483 q) (meaning1488 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1483 = false ∨ valuation q 1488 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-37, -39, -41, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-37, -39, -41, -43])
  have hm := merge_left (literal (valuationOf q) (1475)) (literal (valuationOf q) (1486)) (countLit q [-31, -34, -35]) (countLit q [-37, -39, -41, -43]) (count1485 q) 2 (meaning1475 q) (meaning1486 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1486 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-37, -39, -41, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-37, -39, -41, -43])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1487)) (countLit q [-31, -34, -35]) (countLit q [-37, -39, -41, -43]) (count1485 q) 2 1 (meaning1475 q) (meaning1481 q) (meaning1487 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1481 = false ∨ valuation q 1487 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-31, -34, -35]) + (countLit q [-37, -39, -41, -43]) := List.countP_append (p := literal q) (l₁ := [-31, -34, -35]) (l₂ := [-37, -39, -41, -43])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1488)) (countLit q [-31, -34, -35]) (countLit q [-37, -39, -41, -43]) (count1485 q) 2 2 (meaning1475 q) (meaning1482 q) (meaning1488 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1482 = false ∨ valuation q 1488 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-44]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1492)) (countLit q [-44]) (countLit q [-47]) (count1492 q) 1 (meaningNeg47 q) (meaning1492 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1492 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-44]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1492)) (countLit q [-44]) (countLit q [-47]) (count1492 q) 1 (meaningNeg44 q) (meaning1492 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1492 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 47 = true ∨ valuationOf q 1493 = true := by
  have hs : count1492 q = (countLit q [-44]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (1493)) (countLit q [-44]) (countLit q [-47]) (count1492 q) 1 1 (meaningNeg44 q) (meaningNeg47 q) (meaning1493 q) hs
  change (! (valuationOf q 44)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 47 = true ∨ valuation q 1493 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1494)) (countLit q [-48]) (countLit q [-51]) (count1494 q) 1 (meaningNeg51 q) (meaning1494 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1494 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1494)) (countLit q [-48]) (countLit q [-51]) (count1494 q) 1 (meaningNeg48 q) (meaning1494 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1494 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1495 = true := by
  have hs : count1494 q = (countLit q [-48]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1495)) (countLit q [-48]) (countLit q [-51]) (count1494 q) 1 1 (meaningNeg48 q) (meaningNeg51 q) (meaning1495 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 51 = true ∨ valuation q 1495 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-44, -47]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -47]) (l₂ := [-48, -51])
  have hm := merge_right (literal (valuationOf q) (1494)) (literal (valuationOf q) (1496)) (countLit q [-44, -47]) (countLit q [-48, -51]) (count1496 q) 1 (meaning1494 q) (meaning1496 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1496 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-44, -47]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -47]) (l₂ := [-48, -51])
  have hm := merge_right (literal (valuationOf q) (1495)) (literal (valuationOf q) (1497)) (countLit q [-44, -47]) (countLit q [-48, -51]) (count1496 q) 2 (meaning1495 q) (meaning1497 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1497 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1496 = true := by
  have hs : count1496 q = (countLit q [-44, -47]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -47]) (l₂ := [-48, -51])
  have hm := merge_left (literal (valuationOf q) (1492)) (literal (valuationOf q) (1496)) (countLit q [-44, -47]) (countLit q [-48, -51]) (count1496 q) 1 (meaning1492 q) (meaning1496 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1496 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-44, -47]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -47]) (l₂ := [-48, -51])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1497)) (countLit q [-44, -47]) (countLit q [-48, -51]) (count1496 q) 1 1 (meaning1492 q) (meaning1494 q) (meaning1497 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1494 = false ∨ valuation q 1497 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1498 = true := by
  have hs : count1496 q = (countLit q [-44, -47]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -47]) (l₂ := [-48, -51])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1495)) (literal (valuationOf q) (1498)) (countLit q [-44, -47]) (countLit q [-48, -51]) (count1496 q) 1 2 (meaning1492 q) (meaning1495 q) (meaning1498 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1495 = false ∨ valuation q 1498 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1497 = true := by
  have hs : count1496 q = (countLit q [-44, -47]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -47]) (l₂ := [-48, -51])
  have hm := merge_left (literal (valuationOf q) (1493)) (literal (valuationOf q) (1497)) (countLit q [-44, -47]) (countLit q [-48, -51]) (count1496 q) 2 (meaning1493 q) (meaning1497 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1497 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1498 = true := by
  have hs : count1496 q = (countLit q [-44, -47]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -47]) (l₂ := [-48, -51])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1498)) (countLit q [-44, -47]) (countLit q [-48, -51]) (count1496 q) 2 1 (meaning1493 q) (meaning1494 q) (meaning1498 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1494 = false ∨ valuation q 1498 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1500)) (countLit q [-52]) (countLit q [-54]) (count1500 q) 1 (meaningNeg54 q) (meaning1500 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1500 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1500 = true := by
  have hs : count1500 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1500)) (countLit q [-52]) (countLit q [-54]) (count1500 q) 1 (meaningNeg52 q) (meaning1500 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1500 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1501 = true := by
  have hs : count1500 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1501)) (countLit q [-52]) (countLit q [-54]) (count1500 q) 1 1 (meaningNeg52 q) (meaningNeg54 q) (meaning1501 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 1501 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1502)) (countLit q [-56]) (countLit q [-58]) (count1502 q) 1 (meaningNeg56 q) (meaning1502 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1502 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-52, -54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -58])
  have hm := merge_right (literal (valuationOf q) (1502)) (literal (valuationOf q) (1504)) (countLit q [-52, -54]) (countLit q [-56, -58]) (count1504 q) 1 (meaning1502 q) (meaning1504 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1504 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1504 = true := by
  have hs : count1504 q = (countLit q [-52, -54]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-56, -58])
  have hm := merge_left (literal (valuationOf q) (1500)) (literal (valuationOf q) (1504)) (countLit q [-52, -54]) (countLit q [-56, -58]) (count1504 q) 1 (meaning1500 q) (meaning1504 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1504 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E096.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112096
