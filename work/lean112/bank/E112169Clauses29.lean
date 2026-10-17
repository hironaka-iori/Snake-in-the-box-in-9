import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1519 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1519)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 5 6 (meaning1445 q) (meaning1500 q) (meaning1519 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1500 = false ∨ valuation q 1519 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1520 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1520)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 5 7 (meaning1445 q) (meaning1501 q) (meaning1520 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1501 = false ∨ valuation q 1520 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1521 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1521)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 5 8 (meaning1445 q) (meaning1502 q) (meaning1521 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1502 = false ∨ valuation q 1521 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1516)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 6 2 (meaning1446 q) (meaning1496 q) (meaning1516 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1496 = false ∨ valuation q 1516 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1517)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 6 3 (meaning1446 q) (meaning1497 q) (meaning1517 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1497 = false ∨ valuation q 1517 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1518 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1518)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 6 4 (meaning1446 q) (meaning1498 q) (meaning1518 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1498 = false ∨ valuation q 1518 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1519 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1519)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 6 5 (meaning1446 q) (meaning1499 q) (meaning1519 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1499 = false ∨ valuation q 1519 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1520 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1520)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 6 6 (meaning1446 q) (meaning1500 q) (meaning1520 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1500 = false ∨ valuation q 1520 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1521 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1521)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 6 7 (meaning1446 q) (meaning1501 q) (meaning1521 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1501 = false ∨ valuation q 1521 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1517)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 7 2 (meaning1447 q) (meaning1496 q) (meaning1517 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1496 = false ∨ valuation q 1517 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1518 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1518)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 7 3 (meaning1447 q) (meaning1497 q) (meaning1518 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1497 = false ∨ valuation q 1518 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1519 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1519)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 7 4 (meaning1447 q) (meaning1498 q) (meaning1519 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1498 = false ∨ valuation q 1519 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1520 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1520)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 7 5 (meaning1447 q) (meaning1499 q) (meaning1520 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1499 = false ∨ valuation q 1520 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1519 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1519)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 8 3 (meaning1448 q) (meaning1497 q) (meaning1519 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1497 = false ∨ valuation q 1519 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1520 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1520)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 8 4 (meaning1448 q) (meaning1498 q) (meaning1520 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1498 = false ∨ valuation q 1520 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1522 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1522)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 8 6 (meaning1448 q) (meaning1500 q) (meaning1522 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1500 = false ∨ valuation q 1522 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-59]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1526)) (countLit q [-59]) (countLit q [-63]) (count1526 q) 1 (meaningNeg63 q) (meaning1526 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1526 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-59]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1526)) (countLit q [-59]) (countLit q [-63]) (count1526 q) 1 (meaningNeg59 q) (meaning1526 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1526 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-59]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1527)) (countLit q [-59]) (countLit q [-63]) (count1526 q) 1 1 (meaningNeg59 q) (meaningNeg63 q) (meaning1527 q) hs
  change (! (valuationOf q 59)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 63 = true ∨ valuation q 1527 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-57]) + (countLit q [-59, -63]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59, -63])
  have hm := merge_right (literal (valuationOf q) (1526)) (literal (valuationOf q) (1528)) (countLit q [-57]) (countLit q [-59, -63]) (count1528 q) 1 (meaning1526 q) (meaning1528 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1528 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1529 = true := by
  have hs : count1528 q = (countLit q [-57]) + (countLit q [-59, -63]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59, -63])
  have hm := merge_right (literal (valuationOf q) (1527)) (literal (valuationOf q) (1529)) (countLit q [-57]) (countLit q [-59, -63]) (count1528 q) 2 (meaning1527 q) (meaning1529 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1529 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-57]) + (countLit q [-59, -63]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59, -63])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (1528)) (countLit q [-57]) (countLit q [-59, -63]) (count1528 q) 1 (meaningNeg57 q) (meaning1528 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1528 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1526 = false ∨ valuationOf q 1529 = true := by
  have hs : count1528 q = (countLit q [-57]) + (countLit q [-59, -63]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59, -63])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1529)) (countLit q [-57]) (countLit q [-59, -63]) (count1528 q) 1 1 (meaningNeg57 q) (meaning1526 q) (meaning1529 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1526 = false ∨ valuation q 1529 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (1531)) (countLit q [-65]) (countLit q [-67]) (count1531 q) 1 (meaningNeg67 q) (meaning1531 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1531 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1531)) (countLit q [-65]) (countLit q [-67]) (count1531 q) 1 (meaningNeg65 q) (meaning1531 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1531 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 67 = true ∨ valuationOf q 1532 = true := by
  have hs : count1531 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (1532)) (countLit q [-65]) (countLit q [-67]) (count1531 q) 1 1 (meaningNeg65 q) (meaningNeg67 q) (meaning1532 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 67 = true ∨ valuation q 1532 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1533)) (countLit q [-69]) (countLit q [-70]) (count1533 q) 1 (meaningNeg70 q) (meaning1533 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1533 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1533)) (countLit q [-69]) (countLit q [-70]) (count1533 q) 1 (meaningNeg69 q) (meaning1533 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1533 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 70 = true ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-70)) (literal (valuationOf q) (1534)) (countLit q [-69]) (countLit q [-70]) (count1533 q) 1 1 (meaningNeg69 q) (meaningNeg70 q) (meaning1534 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 70)) = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 1534 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-65, -67]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -70])
  have hm := merge_right (literal (valuationOf q) (1533)) (literal (valuationOf q) (1535)) (countLit q [-65, -67]) (countLit q [-69, -70]) (count1535 q) 1 (meaning1533 q) (meaning1535 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1535 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-65, -67]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -70])
  have hm := merge_right (literal (valuationOf q) (1534)) (literal (valuationOf q) (1536)) (countLit q [-65, -67]) (countLit q [-69, -70]) (count1535 q) 2 (meaning1534 q) (meaning1536 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1536 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-65, -67]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -70])
  have hm := merge_left (literal (valuationOf q) (1531)) (literal (valuationOf q) (1535)) (countLit q [-65, -67]) (countLit q [-69, -70]) (count1535 q) 1 (meaning1531 q) (meaning1535 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1535 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E169.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112169
