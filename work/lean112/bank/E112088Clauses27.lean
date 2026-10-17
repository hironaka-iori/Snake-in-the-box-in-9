import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1488)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 1 5 (meaning1452 q) (meaning1479 q) (meaning1488 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1479 = false ∨ valuation q 1488 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1489)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 1 6 (meaning1452 q) (meaning1480 q) (meaning1489 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1480 = false ∨ valuation q 1489 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1490)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 1 7 (meaning1452 q) (meaning1481 q) (meaning1490 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1481 = false ∨ valuation q 1490 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1452)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1491)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 1 8 (meaning1452 q) (meaning1482 q) (meaning1491 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1482 = false ∨ valuation q 1491 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1486 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1486)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 2 2 (meaning1453 q) (meaning1476 q) (meaning1486 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1476 = false ∨ valuation q 1486 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1487 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1487)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 2 3 (meaning1453 q) (meaning1477 q) (meaning1487 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1477 = false ∨ valuation q 1487 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1488)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 2 4 (meaning1453 q) (meaning1478 q) (meaning1488 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1478 = false ∨ valuation q 1488 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1489)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 2 5 (meaning1453 q) (meaning1479 q) (meaning1489 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1479 = false ∨ valuation q 1489 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1490 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1490)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 2 6 (meaning1453 q) (meaning1480 q) (meaning1490 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1480 = false ∨ valuation q 1490 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1491 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1453)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1491)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 2 7 (meaning1453 q) (meaning1481 q) (meaning1491 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1481 = false ∨ valuation q 1491 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1486 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1486)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 3 1 (meaning1454 q) (meaning1475 q) (meaning1486 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1475 = false ∨ valuation q 1486 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1487 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1487)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 3 2 (meaning1454 q) (meaning1476 q) (meaning1487 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1476 = false ∨ valuation q 1487 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1488 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1488)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 3 3 (meaning1454 q) (meaning1477 q) (meaning1488 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1477 = false ∨ valuation q 1488 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1489 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1489)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 3 4 (meaning1454 q) (meaning1478 q) (meaning1489 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1478 = false ∨ valuation q 1489 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1490)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 3 5 (meaning1454 q) (meaning1479 q) (meaning1490 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1479 = false ∨ valuation q 1490 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1491)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 3 6 (meaning1454 q) (meaning1480 q) (meaning1491 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1480 = false ∨ valuation q 1491 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1492 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1492)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 3 7 (meaning1454 q) (meaning1481 q) (meaning1492 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1481 = false ∨ valuation q 1492 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1487 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1487)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 4 1 (meaning1455 q) (meaning1475 q) (meaning1487 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1475 = false ∨ valuation q 1487 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1488 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1488)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 4 2 (meaning1455 q) (meaning1476 q) (meaning1488 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1476 = false ∨ valuation q 1488 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1489 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1489)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 4 3 (meaning1455 q) (meaning1477 q) (meaning1489 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1477 = false ∨ valuation q 1489 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1490 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1490)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 4 4 (meaning1455 q) (meaning1478 q) (meaning1490 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1478 = false ∨ valuation q 1490 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1491 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1491)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 4 5 (meaning1455 q) (meaning1479 q) (meaning1491 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1479 = false ∨ valuation q 1491 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1492)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 4 6 (meaning1455 q) (meaning1480 q) (meaning1492 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1480 = false ∨ valuation q 1492 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1488 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1488)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 5 1 (meaning1456 q) (meaning1475 q) (meaning1488 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1475 = false ∨ valuation q 1488 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1489 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1489)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 5 2 (meaning1456 q) (meaning1476 q) (meaning1489 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1476 = false ∨ valuation q 1489 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1490 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1490)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 5 3 (meaning1456 q) (meaning1477 q) (meaning1490 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1477 = false ∨ valuation q 1490 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1491 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1491)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 5 4 (meaning1456 q) (meaning1478 q) (meaning1491 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1478 = false ∨ valuation q 1491 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1492 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1492)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 5 5 (meaning1456 q) (meaning1479 q) (meaning1492 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1479 = false ∨ valuation q 1492 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1493 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1493)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 5 6 (meaning1456 q) (meaning1480 q) (meaning1493 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1480 = false ∨ valuation q 1493 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1489 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1489)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 6 1 (meaning1457 q) (meaning1475 q) (meaning1489 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1475 = false ∨ valuation q 1489 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1490 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1490)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 6 2 (meaning1457 q) (meaning1476 q) (meaning1490 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1476 = false ∨ valuation q 1490 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1491 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1491)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 6 3 (meaning1457 q) (meaning1477 q) (meaning1491 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1477 = false ∨ valuation q 1491 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E088.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112088
