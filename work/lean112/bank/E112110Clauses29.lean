import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-45, -46, -48, -49]) + (countLit q [-52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -48, -49]) (l₂ := [-52, -54, -55, -58])
  have hm := merge_left (literal (valuationOf q) (1496)) (literal (valuationOf q) (1508)) (countLit q [-45, -46, -48, -49]) (countLit q [-52, -54, -55, -58]) (count1508 q) 1 (meaning1496 q) (meaning1508 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1508 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-45, -46, -48, -49]) + (countLit q [-52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -48, -49]) (l₂ := [-52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1509)) (countLit q [-45, -46, -48, -49]) (countLit q [-52, -54, -55, -58]) (count1508 q) 1 1 (meaning1496 q) (meaning1504 q) (meaning1509 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1504 = false ∨ valuation q 1509 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-45, -46, -48, -49]) + (countLit q [-52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -48, -49]) (l₂ := [-52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1496)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1510)) (countLit q [-45, -46, -48, -49]) (countLit q [-52, -54, -55, -58]) (count1508 q) 1 2 (meaning1496 q) (meaning1505 q) (meaning1510 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1505 = false ∨ valuation q 1510 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-45, -46, -48, -49]) + (countLit q [-52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -48, -49]) (l₂ := [-52, -54, -55, -58])
  have hm := merge_left (literal (valuationOf q) (1497)) (literal (valuationOf q) (1509)) (countLit q [-45, -46, -48, -49]) (countLit q [-52, -54, -55, -58]) (count1508 q) 2 (meaning1497 q) (meaning1509 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1509 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1497 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-45, -46, -48, -49]) + (countLit q [-52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -48, -49]) (l₂ := [-52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1497)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1510)) (countLit q [-45, -46, -48, -49]) (countLit q [-52, -54, -55, -58]) (count1508 q) 2 1 (meaning1497 q) (meaning1504 q) (meaning1510 q) hs
  change valuationOf q 1497 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1497 = false ∨ valuation q 1504 = false ∨ valuation q 1510 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1510 = true := by
  have hs : count1508 q = (countLit q [-45, -46, -48, -49]) + (countLit q [-52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -48, -49]) (l₂ := [-52, -54, -55, -58])
  have hm := merge_left (literal (valuationOf q) (1498)) (literal (valuationOf q) (1510)) (countLit q [-45, -46, -48, -49]) (countLit q [-52, -54, -55, -58]) (count1508 q) 3 (meaning1498 q) (meaning1510 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1510 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1511 = true := by
  have hs : count1508 q = (countLit q [-45, -46, -48, -49]) + (countLit q [-52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -48, -49]) (l₂ := [-52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1498)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1511)) (countLit q [-45, -46, -48, -49]) (countLit q [-52, -54, -55, -58]) (count1508 q) 3 1 (meaning1498 q) (meaning1504 q) (meaning1511 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1504 = false ∨ valuation q 1511 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1516 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1516)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 1 (meaning1508 q) (meaning1516 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1516 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1517 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1517)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 2 (meaning1509 q) (meaning1517 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1517 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1518 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1510)) (literal (valuationOf q) (1518)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 3 (meaning1510 q) (meaning1518 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1518 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1516 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_left (literal (valuationOf q) (1485)) (literal (valuationOf q) (1516)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 1 (meaning1485 q) (meaning1516 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1516 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1517 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1517)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 1 1 (meaning1485 q) (meaning1508 q) (meaning1517 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1508 = false ∨ valuation q 1517 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1518 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1518)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 1 2 (meaning1485 q) (meaning1509 q) (meaning1518 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1509 = false ∨ valuation q 1518 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1519 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1519)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 1 3 (meaning1485 q) (meaning1510 q) (meaning1519 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1510 = false ∨ valuation q 1519 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1520 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1520)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 1 4 (meaning1485 q) (meaning1511 q) (meaning1520 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1511 = false ∨ valuation q 1520 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1517 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_left (literal (valuationOf q) (1486)) (literal (valuationOf q) (1517)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 2 (meaning1486 q) (meaning1517 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1517 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1518 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1518)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 2 1 (meaning1486 q) (meaning1508 q) (meaning1518 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1508 = false ∨ valuation q 1518 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1519 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1519)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 2 2 (meaning1486 q) (meaning1509 q) (meaning1519 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1509 = false ∨ valuation q 1519 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1520 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1520)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 2 3 (meaning1486 q) (meaning1510 q) (meaning1520 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1510 = false ∨ valuation q 1520 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1518 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_left (literal (valuationOf q) (1487)) (literal (valuationOf q) (1518)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 3 (meaning1487 q) (meaning1518 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1518 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1519 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1519)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 3 1 (meaning1487 q) (meaning1508 q) (meaning1519 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1508 = false ∨ valuation q 1519 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1520 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1520)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 3 2 (meaning1487 q) (meaning1509 q) (meaning1520 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1509 = false ∨ valuation q 1520 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1521 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1521)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 3 3 (meaning1487 q) (meaning1510 q) (meaning1521 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1510 = false ∨ valuation q 1521 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1519 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_left (literal (valuationOf q) (1488)) (literal (valuationOf q) (1519)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 4 (meaning1488 q) (meaning1519 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1519 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1520 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1520)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 4 1 (meaning1488 q) (meaning1508 q) (meaning1520 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1508 = false ∨ valuation q 1520 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1521 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1521)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 4 2 (meaning1488 q) (meaning1509 q) (meaning1521 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1509 = false ∨ valuation q 1521 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1520 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_left (literal (valuationOf q) (1489)) (literal (valuationOf q) (1520)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 5 (meaning1489 q) (meaning1520 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1520 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1521 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1521)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 5 1 (meaning1489 q) (meaning1508 q) (meaning1521 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1508 = false ∨ valuation q 1521 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1522 = true := by
  have hs : count1516 q = (countLit q [-30, -32, -35, -37, -38, -40, -42]) + (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -35, -37, -38, -40, -42]) (l₂ := [-45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1522)) (countLit q [-30, -32, -35, -37, -38, -40, -42]) (countLit q [-45, -46, -48, -49, -52, -54, -55, -58]) (count1516 q) 5 2 (meaning1489 q) (meaning1509 q) (meaning1522 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1509 = false ∨ valuation q 1522 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1536 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1536)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 2 4 (meaning1458 q) (meaning1519 q) (meaning1536 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1519 = false ∨ valuation q 1536 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1535 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1535)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 3 2 (meaning1459 q) (meaning1517 q) (meaning1535 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1517 = false ∨ valuation q 1535 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1536 = true := by
  have hs : count1531 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) + (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (l₂ := [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1536)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29]) (countLit q [-30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (count1531 q) 3 3 (meaning1459 q) (meaning1518 q) (meaning1536 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1518 = false ∨ valuation q 1536 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E110.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112110
