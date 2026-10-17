import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1500 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1500)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 5 1 (meaning1472 q) (meaning1488 q) (meaning1500 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1488 = false ∨ valuation q 1500 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1501 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1501)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 5 2 (meaning1472 q) (meaning1489 q) (meaning1501 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1489 = false ∨ valuation q 1501 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1502 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1502)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 5 3 (meaning1472 q) (meaning1490 q) (meaning1502 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1490 = false ∨ valuation q 1502 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1503 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1503)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 5 4 (meaning1472 q) (meaning1491 q) (meaning1503 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1491 = false ∨ valuation q 1503 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1500 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_left (literal (valuationOf q) (1473)) (literal (valuationOf q) (1500)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 6 (meaning1473 q) (meaning1500 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1500 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1501 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1501)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 6 1 (meaning1473 q) (meaning1488 q) (meaning1501 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1488 = false ∨ valuation q 1501 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1502 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1502)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 6 2 (meaning1473 q) (meaning1489 q) (meaning1502 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1489 = false ∨ valuation q 1502 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1503 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1503)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 6 3 (meaning1473 q) (meaning1490 q) (meaning1503 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1490 = false ∨ valuation q 1503 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1501 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_left (literal (valuationOf q) (1474)) (literal (valuationOf q) (1501)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 7 (meaning1474 q) (meaning1501 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1501 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1502 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1502)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 7 1 (meaning1474 q) (meaning1488 q) (meaning1502 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1488 = false ∨ valuation q 1502 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1503 = true := by
  have hs : count1495 q = (countLit q [-30, -31, -35, -36, -38, -40, -42]) + (countLit q [-43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-30, -31, -35, -36, -38, -40, -42]) (l₂ := [-43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1503)) (countLit q [-30, -31, -35, -36, -38, -40, -42]) (countLit q [-43, -45, -46, -49, -51, -52, -55]) (count1495 q) 7 2 (meaning1474 q) (meaning1489 q) (meaning1503 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1489 = false ∨ valuation q 1503 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1516)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 1 7 (meaning1441 q) (meaning1501 q) (meaning1516 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1501 = false ∨ valuation q 1516 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1517)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 1 8 (meaning1441 q) (meaning1502 q) (meaning1517 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1502 = false ∨ valuation q 1517 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1518 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1518)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 1 9 (meaning1441 q) (meaning1503 q) (meaning1518 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1503 = false ∨ valuation q 1518 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1516)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 2 6 (meaning1442 q) (meaning1500 q) (meaning1516 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1500 = false ∨ valuation q 1516 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1517)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 2 7 (meaning1442 q) (meaning1501 q) (meaning1517 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1501 = false ∨ valuation q 1517 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1518 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1518)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 2 8 (meaning1442 q) (meaning1502 q) (meaning1518 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1502 = false ∨ valuation q 1518 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1519 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1519)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 2 9 (meaning1442 q) (meaning1503 q) (meaning1519 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1503 = false ∨ valuation q 1519 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1516)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 3 5 (meaning1443 q) (meaning1499 q) (meaning1516 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1499 = false ∨ valuation q 1516 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1517)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 3 6 (meaning1443 q) (meaning1500 q) (meaning1517 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1500 = false ∨ valuation q 1517 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1518 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1518)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 3 7 (meaning1443 q) (meaning1501 q) (meaning1518 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1501 = false ∨ valuation q 1518 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1519 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1519)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 3 8 (meaning1443 q) (meaning1502 q) (meaning1519 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1502 = false ∨ valuation q 1519 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1520 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1520)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 3 9 (meaning1443 q) (meaning1503 q) (meaning1520 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1503 = false ∨ valuation q 1520 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1516)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 4 4 (meaning1444 q) (meaning1498 q) (meaning1516 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1498 = false ∨ valuation q 1516 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1517)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 4 5 (meaning1444 q) (meaning1499 q) (meaning1517 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1499 = false ∨ valuation q 1517 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1518 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1518)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 4 6 (meaning1444 q) (meaning1500 q) (meaning1518 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1500 = false ∨ valuation q 1518 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1519 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1519)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 4 7 (meaning1444 q) (meaning1501 q) (meaning1519 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1501 = false ∨ valuation q 1519 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1520 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1520)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 4 8 (meaning1444 q) (meaning1502 q) (meaning1520 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1502 = false ∨ valuation q 1520 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1521 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1521)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 4 9 (meaning1444 q) (meaning1503 q) (meaning1521 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1503 = false ∨ valuation q 1521 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1516)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 5 3 (meaning1445 q) (meaning1497 q) (meaning1516 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1497 = false ∨ valuation q 1516 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1517)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 5 4 (meaning1445 q) (meaning1498 q) (meaning1517 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1498 = false ∨ valuation q 1517 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1518 = true := by
  have hs : count1509 q = (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) + (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (l₂ := [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1518)) (countLit q [-2, -4, -5, -8, -9, -12, -13, -17, -18, -19, -21, -24, -25, -27]) (countLit q [-30, -31, -35, -36, -38, -40, -42, -43, -45, -46, -49, -51, -52, -55]) (count1509 q) 5 5 (meaning1445 q) (meaning1499 q) (meaning1518 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1499 = false ∨ valuation q 1518 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E169.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112169
