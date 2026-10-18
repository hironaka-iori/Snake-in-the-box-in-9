import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1551 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1551)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 2 5 (meaning1478 q) (meaning1535 q) (meaning1551 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1535 = false ∨ valuation q 1551 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1552 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1552)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 2 6 (meaning1478 q) (meaning1536 q) (meaning1552 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1536 = false ∨ valuation q 1552 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1553 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1553)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 2 7 (meaning1478 q) (meaning1537 q) (meaning1553 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1537 = false ∨ valuation q 1553 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1549)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 3 2 (meaning1479 q) (meaning1532 q) (meaning1549 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1532 = false ∨ valuation q 1549 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1550)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 3 3 (meaning1479 q) (meaning1533 q) (meaning1550 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1533 = false ∨ valuation q 1550 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1551 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1551)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 3 4 (meaning1479 q) (meaning1534 q) (meaning1551 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1534 = false ∨ valuation q 1551 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1552 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1552)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 3 5 (meaning1479 q) (meaning1535 q) (meaning1552 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1535 = false ∨ valuation q 1552 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1553 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1553)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 3 6 (meaning1479 q) (meaning1536 q) (meaning1553 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1536 = false ∨ valuation q 1553 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1554 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1554)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 3 7 (meaning1479 q) (meaning1537 q) (meaning1554 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1537 = false ∨ valuation q 1554 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1549)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 4 1 (meaning1480 q) (meaning1531 q) (meaning1549 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1531 = false ∨ valuation q 1549 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1550)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 4 2 (meaning1480 q) (meaning1532 q) (meaning1550 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1532 = false ∨ valuation q 1550 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1551 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1551)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 4 3 (meaning1480 q) (meaning1533 q) (meaning1551 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1533 = false ∨ valuation q 1551 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1552 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1552)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 4 4 (meaning1480 q) (meaning1534 q) (meaning1552 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1534 = false ∨ valuation q 1552 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1553 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1553)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 4 5 (meaning1480 q) (meaning1535 q) (meaning1553 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1535 = false ∨ valuation q 1553 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1554 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1554)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 4 6 (meaning1480 q) (meaning1536 q) (meaning1554 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1536 = false ∨ valuation q 1554 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1550)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 5 1 (meaning1481 q) (meaning1531 q) (meaning1550 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1531 = false ∨ valuation q 1550 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1551 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1551)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 5 2 (meaning1481 q) (meaning1532 q) (meaning1551 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1532 = false ∨ valuation q 1551 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1552 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1552)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 5 3 (meaning1481 q) (meaning1533 q) (meaning1552 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1533 = false ∨ valuation q 1552 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1553 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1553)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 5 4 (meaning1481 q) (meaning1534 q) (meaning1553 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1534 = false ∨ valuation q 1553 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1554 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1554)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 5 5 (meaning1481 q) (meaning1535 q) (meaning1554 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1535 = false ∨ valuation q 1554 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1555 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1555)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 5 6 (meaning1481 q) (meaning1536 q) (meaning1555 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1536 = false ∨ valuation q 1555 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1552 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1552)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 6 2 (meaning1482 q) (meaning1532 q) (meaning1552 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1532 = false ∨ valuation q 1552 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1553 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1553)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 6 3 (meaning1482 q) (meaning1533 q) (meaning1553 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1533 = false ∨ valuation q 1553 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1554 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1554)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 6 4 (meaning1482 q) (meaning1534 q) (meaning1554 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1534 = false ∨ valuation q 1554 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1555 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1555)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 6 5 (meaning1482 q) (meaning1535 q) (meaning1555 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1535 = false ∨ valuation q 1555 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1553 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1553)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 7 2 (meaning1483 q) (meaning1532 q) (meaning1553 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1532 = false ∨ valuation q 1553 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1554 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1554)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 7 3 (meaning1483 q) (meaning1533 q) (meaning1554 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1533 = false ∨ valuation q 1554 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1555 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1555)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 7 4 (meaning1483 q) (meaning1534 q) (meaning1555 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1534 = false ∨ valuation q 1555 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1556 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1556)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 7 5 (meaning1483 q) (meaning1535 q) (meaning1556 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1535 = false ∨ valuation q 1556 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1555 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1484)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1555)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 8 3 (meaning1484 q) (meaning1533 q) (meaning1555 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1533 = false ∨ valuation q 1555 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1556 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1484)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1556)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 8 4 (meaning1484 q) (meaning1534 q) (meaning1556 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1534 = false ∨ valuation q 1556 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1556 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1556)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 9 3 (meaning1485 q) (meaning1533 q) (meaning1556 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1533 = false ∨ valuation q 1556 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E027.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112027
