import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1527 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1527)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 2 2 (meaning1514 q) (meaning1521 q) (meaning1527 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1521 = false ∨ valuation q 1527 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1528 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1522)) (literal (valuationOf q) (1528)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 2 3 (meaning1514 q) (meaning1522 q) (meaning1528 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1522 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1522 = false ∨ valuation q 1528 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1529 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1529)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 2 4 (meaning1514 q) (meaning1523 q) (meaning1529 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1523 = false ∨ valuation q 1529 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1528 = true := by
  have hs : count1524 q = (countLit q [-47, -48, -52]) + (countLit q [-54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -52]) (l₂ := [-54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1528)) (countLit q [-47, -48, -52]) (countLit q [-54, -55, -56, -57]) (count1524 q) 3 2 (meaning1515 q) (meaning1521 q) (meaning1528 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1521 = false ∨ valuation q 1528 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1524)) (literal (valuationOf q) (1531)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 1 (meaning1524 q) (meaning1531 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1531 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1532 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1525)) (literal (valuationOf q) (1532)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 2 (meaning1525 q) (meaning1532 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1532 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1533 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1526)) (literal (valuationOf q) (1533)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 3 (meaning1526 q) (meaning1533 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1533 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1534 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1527)) (literal (valuationOf q) (1534)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 4 (meaning1527 q) (meaning1534 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1534 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1535 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1528)) (literal (valuationOf q) (1535)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 5 (meaning1528 q) (meaning1535 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1535 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1536 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1529)) (literal (valuationOf q) (1536)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 6 (meaning1529 q) (meaning1536 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1536 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1504)) (literal (valuationOf q) (1531)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 1 (meaning1504 q) (meaning1531 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1531 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1532 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1532)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 1 1 (meaning1504 q) (meaning1524 q) (meaning1532 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1524 = false ∨ valuation q 1532 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1533 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1533)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 1 2 (meaning1504 q) (meaning1525 q) (meaning1533 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1525 = false ∨ valuation q 1533 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1534 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1534)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 1 3 (meaning1504 q) (meaning1526 q) (meaning1534 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1526 = false ∨ valuation q 1534 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1535 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1535)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 1 4 (meaning1504 q) (meaning1527 q) (meaning1535 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1527 = false ∨ valuation q 1535 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1536 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1536)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 1 5 (meaning1504 q) (meaning1528 q) (meaning1536 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1528 = false ∨ valuation q 1536 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1533 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1533)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 2 1 (meaning1505 q) (meaning1524 q) (meaning1533 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1524 = false ∨ valuation q 1533 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1534 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1534)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 2 2 (meaning1505 q) (meaning1525 q) (meaning1534 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1525 = false ∨ valuation q 1534 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1535 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1535)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 2 3 (meaning1505 q) (meaning1526 q) (meaning1535 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1526 = false ∨ valuation q 1535 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1536 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1536)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 2 4 (meaning1505 q) (meaning1527 q) (meaning1536 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1527 = false ∨ valuation q 1536 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1537 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1537)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 2 5 (meaning1505 q) (meaning1528 q) (meaning1537 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1528 = false ∨ valuation q 1537 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1534 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1534)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 3 1 (meaning1506 q) (meaning1524 q) (meaning1534 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1524 = false ∨ valuation q 1534 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1535 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1535)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 3 2 (meaning1506 q) (meaning1525 q) (meaning1535 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1525 = false ∨ valuation q 1535 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1536 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1536)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 3 3 (meaning1506 q) (meaning1526 q) (meaning1536 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1526 = false ∨ valuation q 1536 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1537 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1537)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 3 4 (meaning1506 q) (meaning1527 q) (meaning1537 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1527 = false ∨ valuation q 1537 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1535 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1535)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 4 1 (meaning1507 q) (meaning1524 q) (meaning1535 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1524 = false ∨ valuation q 1535 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1537 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1537)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 4 3 (meaning1507 q) (meaning1526 q) (meaning1537 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1526 = false ∨ valuation q 1537 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1537 = true := by
  have hs : count1531 q = (countLit q [-32, -35, -38, -39, -41, -45, -46]) + (countLit q [-47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -38, -39, -41, -45, -46]) (l₂ := [-47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1537)) (countLit q [-32, -35, -38, -39, -41, -45, -46]) (countLit q [-47, -48, -52, -54, -55, -56, -57]) (count1531 q) 5 2 (meaning1508 q) (meaning1525 q) (meaning1537 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1525 = false ∨ valuation q 1537 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1550)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 1 5 (meaning1477 q) (meaning1535 q) (meaning1550 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1535 = false ∨ valuation q 1550 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1548 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1548)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 2 2 (meaning1478 q) (meaning1532 q) (meaning1548 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1532 = false ∨ valuation q 1548 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1549)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 2 3 (meaning1478 q) (meaning1533 q) (meaning1549 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1533 = false ∨ valuation q 1549 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) + (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (l₂ := [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1550)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29]) (countLit q [-32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (count1545 q) 2 4 (meaning1478 q) (meaning1534 q) (meaning1550 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1534 = false ∨ valuation q 1550 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E027.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112027
