import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1490)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 1 2 (meaning1477 q) (meaning1485 q) (meaning1490 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1485 = false ∨ valuation q 1490 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1491 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1486)) (literal (valuationOf q) (1491)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 1 3 (meaning1477 q) (meaning1486 q) (meaning1491 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1486 = false ∨ valuation q 1491 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_left (literal (valuationOf q) (1478)) (literal (valuationOf q) (1489)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 2 (meaning1478 q) (meaning1489 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1489 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1490)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 2 1 (meaning1478 q) (meaning1484 q) (meaning1490 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1484 = false ∨ valuation q 1490 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1491 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1491)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 2 2 (meaning1478 q) (meaning1485 q) (meaning1491 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1485 = false ∨ valuation q 1491 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1492 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1486)) (literal (valuationOf q) (1492)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 2 3 (meaning1478 q) (meaning1486 q) (meaning1492 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1486 = false ∨ valuation q 1492 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_left (literal (valuationOf q) (1479)) (literal (valuationOf q) (1490)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 3 (meaning1479 q) (meaning1490 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1490 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1491 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1491)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 3 1 (meaning1479 q) (meaning1484 q) (meaning1491 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1484 = false ∨ valuation q 1491 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1492 = true := by
  have hs : count1488 q = (countLit q [-43, -45, -46]) + (countLit q [-49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-43, -45, -46]) (l₂ := [-49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1492)) (countLit q [-43, -45, -46]) (countLit q [-49, -51, -52, -55]) (count1488 q) 3 2 (meaning1479 q) (meaning1485 q) (meaning1492 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1485 = false ∨ valuation q 1492 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1496 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1496)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 1 1 (meaning1468 q) (meaning1488 q) (meaning1496 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1488 = false ∨ valuation q 1496 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1497 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1497)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 1 2 (meaning1468 q) (meaning1489 q) (meaning1497 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1489 = false ∨ valuation q 1497 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1498 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1498)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 1 3 (meaning1468 q) (meaning1490 q) (meaning1498 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1490 = false ∨ valuation q 1498 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1499 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1499)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 1 4 (meaning1468 q) (meaning1491 q) (meaning1499 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1491 = false ∨ valuation q 1499 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1500 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1500)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 1 5 (meaning1468 q) (meaning1492 q) (meaning1500 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1492 = false ∨ valuation q 1500 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1496 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_left (literal (valuationOf q) (1469)) (literal (valuationOf q) (1496)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 2 (meaning1469 q) (meaning1496 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1496 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1497 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1497)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 2 1 (meaning1469 q) (meaning1488 q) (meaning1497 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1488 = false ∨ valuation q 1497 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1498 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1498)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 2 2 (meaning1469 q) (meaning1489 q) (meaning1498 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1489 = false ∨ valuation q 1498 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1499 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1499)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 2 3 (meaning1469 q) (meaning1490 q) (meaning1499 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1490 = false ∨ valuation q 1499 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1500 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1500)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 2 4 (meaning1469 q) (meaning1491 q) (meaning1500 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1491 = false ∨ valuation q 1500 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1501 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1501)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 2 5 (meaning1469 q) (meaning1492 q) (meaning1501 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1492 = false ∨ valuation q 1501 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1497 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_left (literal (valuationOf q) (1470)) (literal (valuationOf q) (1497)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 3 (meaning1470 q) (meaning1497 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1497 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1498 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1498)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 3 1 (meaning1470 q) (meaning1488 q) (meaning1498 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1488 = false ∨ valuation q 1498 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1499 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1499)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 3 2 (meaning1470 q) (meaning1489 q) (meaning1499 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1489 = false ∨ valuation q 1499 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1500 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1500)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 3 3 (meaning1470 q) (meaning1490 q) (meaning1500 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1490 = false ∨ valuation q 1500 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1501 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1501)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 3 4 (meaning1470 q) (meaning1491 q) (meaning1501 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1491 = false ∨ valuation q 1501 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1502 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1502)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 3 5 (meaning1470 q) (meaning1492 q) (meaning1502 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1492 = false ∨ valuation q 1502 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1498 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_left (literal (valuationOf q) (1471)) (literal (valuationOf q) (1498)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 4 (meaning1471 q) (meaning1498 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1498 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1499 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1499)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 4 1 (meaning1471 q) (meaning1488 q) (meaning1499 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1488 = false ∨ valuation q 1499 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1500 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1500)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 4 2 (meaning1471 q) (meaning1489 q) (meaning1500 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1489 = false ∨ valuation q 1500 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1501 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1501)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 4 3 (meaning1471 q) (meaning1490 q) (meaning1501 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1490 = false ∨ valuation q 1501 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1502 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1502)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 4 4 (meaning1471 q) (meaning1491 q) (meaning1502 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1491 = false ∨ valuation q 1502 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1499 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_left (literal (valuationOf q) (1472)) (literal (valuationOf q) (1499)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 5 (meaning1472 q) (meaning1499 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1499 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E169.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112169
