import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1507 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1507)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 6 1 (meaning1475 q) (meaning1493 q) (meaning1507 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1493 = false ∨ valuation q 1507 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1508 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1508)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 6 2 (meaning1475 q) (meaning1494 q) (meaning1508 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1494 = false ∨ valuation q 1508 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1509 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1495)) (literal (valuationOf q) (1509)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 6 3 (meaning1475 q) (meaning1495 q) (meaning1509 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1495 = false ∨ valuation q 1509 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1525 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1525)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 3 7 (meaning1445 q) (meaning1507 q) (meaning1525 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1507 = false ∨ valuation q 1525 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1527 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1527)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 3 9 (meaning1445 q) (meaning1509 q) (meaning1527 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1509 = false ∨ valuation q 1527 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1521 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1521)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 4 2 (meaning1446 q) (meaning1502 q) (meaning1521 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1502 = false ∨ valuation q 1521 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1522 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1522)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 4 3 (meaning1446 q) (meaning1503 q) (meaning1522 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1503 = false ∨ valuation q 1522 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1523 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1523)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 4 4 (meaning1446 q) (meaning1504 q) (meaning1523 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1504 = false ∨ valuation q 1523 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1524 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1524)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 4 5 (meaning1446 q) (meaning1505 q) (meaning1524 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1505 = false ∨ valuation q 1524 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1525 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1525)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 4 6 (meaning1446 q) (meaning1506 q) (meaning1525 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1506 = false ∨ valuation q 1525 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1526 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1526)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 4 7 (meaning1446 q) (meaning1507 q) (meaning1526 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1507 = false ∨ valuation q 1526 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1527 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1527)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 4 8 (meaning1446 q) (meaning1508 q) (meaning1527 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1508 = false ∨ valuation q 1527 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1528 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1528)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 4 9 (meaning1446 q) (meaning1509 q) (meaning1528 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1509 = false ∨ valuation q 1528 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1523 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1523)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 5 3 (meaning1447 q) (meaning1503 q) (meaning1523 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1503 = false ∨ valuation q 1523 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1524 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1524)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 5 4 (meaning1447 q) (meaning1504 q) (meaning1524 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1504 = false ∨ valuation q 1524 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1525 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1525)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 5 5 (meaning1447 q) (meaning1505 q) (meaning1525 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1505 = false ∨ valuation q 1525 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1526 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1526)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 5 6 (meaning1447 q) (meaning1506 q) (meaning1526 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1506 = false ∨ valuation q 1526 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1527 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1527)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 5 7 (meaning1447 q) (meaning1507 q) (meaning1527 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1507 = false ∨ valuation q 1527 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1528 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1528)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 5 8 (meaning1447 q) (meaning1508 q) (meaning1528 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1508 = false ∨ valuation q 1528 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1529 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1529)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 5 9 (meaning1447 q) (meaning1509 q) (meaning1529 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1509 = false ∨ valuation q 1529 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1524 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1524)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 6 3 (meaning1448 q) (meaning1503 q) (meaning1524 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1503 = false ∨ valuation q 1524 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1525 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1525)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 6 4 (meaning1448 q) (meaning1504 q) (meaning1525 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1504 = false ∨ valuation q 1525 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1526 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1526)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 6 5 (meaning1448 q) (meaning1505 q) (meaning1526 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1505 = false ∨ valuation q 1526 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1527 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1527)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 6 6 (meaning1448 q) (meaning1506 q) (meaning1527 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1506 = false ∨ valuation q 1527 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1528 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1528)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 6 7 (meaning1448 q) (meaning1507 q) (meaning1528 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1507 = false ∨ valuation q 1528 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1529 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1529)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 6 8 (meaning1448 q) (meaning1508 q) (meaning1529 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1508 = false ∨ valuation q 1529 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1525 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1503)) (literal (valuationOf q) (1525)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 7 3 (meaning1449 q) (meaning1503 q) (meaning1525 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1503 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1503 = false ∨ valuation q 1525 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1526 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1504)) (literal (valuationOf q) (1526)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 7 4 (meaning1449 q) (meaning1504 q) (meaning1526 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1504 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1504 = false ∨ valuation q 1526 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1527 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1527)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 7 5 (meaning1449 q) (meaning1505 q) (meaning1527 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1505 = false ∨ valuation q 1527 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1528 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1528)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 7 6 (meaning1449 q) (meaning1506 q) (meaning1528 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1506 = false ∨ valuation q 1528 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1529 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1529)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 7 7 (meaning1449 q) (meaning1507 q) (meaning1529 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1507 = false ∨ valuation q 1529 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1530 = true := by
  have hs : count1516 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) + (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (l₂ := [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1530)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -16, -19, -20, -22, -24, -25, -26]) (countLit q [-27, -29, -30, -33, -35, -37, -41, -43, -44, -46, -49, -50, -51, -52, -56]) (count1516 q) 7 8 (meaning1449 q) (meaning1508 q) (meaning1530 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1508 = false ∨ valuation q 1530 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E064.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112064
