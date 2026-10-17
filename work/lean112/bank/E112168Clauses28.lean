import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1487 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1487)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 4 3 (meaning1416 q) (meaning1469 q) (meaning1487 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1469 = false ∨ valuation q 1487 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1488 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1488)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 4 4 (meaning1416 q) (meaning1470 q) (meaning1488 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1470 = false ∨ valuation q 1488 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1489 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1489)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 4 5 (meaning1416 q) (meaning1471 q) (meaning1489 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1471 = false ∨ valuation q 1489 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1490 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1490)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 4 6 (meaning1416 q) (meaning1472 q) (meaning1490 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1472 = false ∨ valuation q 1490 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1491 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1491)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 4 7 (meaning1416 q) (meaning1473 q) (meaning1491 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1473 = false ∨ valuation q 1491 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1492 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1492)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 4 8 (meaning1416 q) (meaning1474 q) (meaning1492 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1474 = false ∨ valuation q 1492 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1487 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1487)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 5 2 (meaning1417 q) (meaning1468 q) (meaning1487 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1468 = false ∨ valuation q 1487 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1488 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1488)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 5 3 (meaning1417 q) (meaning1469 q) (meaning1488 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1469 = false ∨ valuation q 1488 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1489 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1489)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 5 4 (meaning1417 q) (meaning1470 q) (meaning1489 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1470 = false ∨ valuation q 1489 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1490 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1490)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 5 5 (meaning1417 q) (meaning1471 q) (meaning1490 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1471 = false ∨ valuation q 1490 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1491 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1491)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 5 6 (meaning1417 q) (meaning1472 q) (meaning1491 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1472 = false ∨ valuation q 1491 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1492 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1492)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 5 7 (meaning1417 q) (meaning1473 q) (meaning1492 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1473 = false ∨ valuation q 1492 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1493 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1493)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 5 8 (meaning1417 q) (meaning1474 q) (meaning1493 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1474 = false ∨ valuation q 1493 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1488 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1488)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 6 2 (meaning1418 q) (meaning1468 q) (meaning1488 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1468 = false ∨ valuation q 1488 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1489 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1489)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 6 3 (meaning1418 q) (meaning1469 q) (meaning1489 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1469 = false ∨ valuation q 1489 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1490 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1490)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 6 4 (meaning1418 q) (meaning1470 q) (meaning1490 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1470 = false ∨ valuation q 1490 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1491 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1491)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 6 5 (meaning1418 q) (meaning1471 q) (meaning1491 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1471 = false ∨ valuation q 1491 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1492 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1492)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 6 6 (meaning1418 q) (meaning1472 q) (meaning1492 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1472 = false ∨ valuation q 1492 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1493 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1493)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 6 7 (meaning1418 q) (meaning1473 q) (meaning1493 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1473 = false ∨ valuation q 1493 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1489 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1489)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 7 2 (meaning1419 q) (meaning1468 q) (meaning1489 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1468 = false ∨ valuation q 1489 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1490 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1490)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 7 3 (meaning1419 q) (meaning1469 q) (meaning1490 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1469 = false ∨ valuation q 1490 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1491 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1491)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 7 4 (meaning1419 q) (meaning1470 q) (meaning1491 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1470 = false ∨ valuation q 1491 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1492 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1492)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 7 5 (meaning1419 q) (meaning1471 q) (meaning1492 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1471 = false ∨ valuation q 1492 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1493 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1493)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 7 6 (meaning1419 q) (meaning1472 q) (meaning1493 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1472 = false ∨ valuation q 1493 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1490 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1420)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1490)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 8 2 (meaning1420 q) (meaning1468 q) (meaning1490 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1468 = false ∨ valuation q 1490 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1491 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1420)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1491)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 8 3 (meaning1420 q) (meaning1469 q) (meaning1491 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1469 = false ∨ valuation q 1491 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1492 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1420)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1492)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 8 4 (meaning1420 q) (meaning1470 q) (meaning1492 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1470 = false ∨ valuation q 1492 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1493 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1420)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1493)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 8 5 (meaning1420 q) (meaning1471 q) (meaning1493 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1471 = false ∨ valuation q 1493 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1491 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1421)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1491)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 9 2 (meaning1421 q) (meaning1468 q) (meaning1491 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1468 = false ∨ valuation q 1491 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1492 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1421)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1492)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 9 3 (meaning1421 q) (meaning1469 q) (meaning1492 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1469 = false ∨ valuation q 1492 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1493 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1421)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1493)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 9 4 (meaning1421 q) (meaning1470 q) (meaning1493 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1470 = false ∨ valuation q 1493 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1492 = true := by
  have hs : count1481 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) + (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (l₂ := [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58])
  have hm := merge_two (literal (valuationOf q) (1422)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1492)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]) (countLit q [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (count1481 q) 10 2 (meaning1422 q) (meaning1468 q) (meaning1492 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1468 = false ∨ valuation q 1492 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E168.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112168
