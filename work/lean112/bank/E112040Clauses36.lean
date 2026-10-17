import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1550 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1550)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 3 4 (meaning1515 q) (meaning1539 q) (meaning1550 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1539 = false ∨ valuation q 1550 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1551 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1551)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 3 5 (meaning1515 q) (meaning1540 q) (meaning1551 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1540 = false ∨ valuation q 1551 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1553)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 3 7 (meaning1515 q) (meaning1542 q) (meaning1553 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1542 = false ∨ valuation q 1553 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1548 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1548)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 4 1 (meaning1516 q) (meaning1536 q) (meaning1548 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1536 = false ∨ valuation q 1548 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1549 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1549)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 4 2 (meaning1516 q) (meaning1537 q) (meaning1549 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1537 = false ∨ valuation q 1549 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1550 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1550)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 4 3 (meaning1516 q) (meaning1538 q) (meaning1550 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1538 = false ∨ valuation q 1550 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1551 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1551)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 4 4 (meaning1516 q) (meaning1539 q) (meaning1551 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1539 = false ∨ valuation q 1551 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1552 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1552)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 4 5 (meaning1516 q) (meaning1540 q) (meaning1552 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1540 = false ∨ valuation q 1552 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1554)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 4 7 (meaning1516 q) (meaning1542 q) (meaning1554 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1542 = false ∨ valuation q 1554 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1549 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1549)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 5 1 (meaning1517 q) (meaning1536 q) (meaning1549 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1536 = false ∨ valuation q 1549 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1550 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1550)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 5 2 (meaning1517 q) (meaning1537 q) (meaning1550 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1537 = false ∨ valuation q 1550 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1551 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1551)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 5 3 (meaning1517 q) (meaning1538 q) (meaning1551 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1538 = false ∨ valuation q 1551 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1552 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1552)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 5 4 (meaning1517 q) (meaning1539 q) (meaning1552 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1539 = false ∨ valuation q 1552 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1553 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1553)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 5 5 (meaning1517 q) (meaning1540 q) (meaning1553 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1540 = false ∨ valuation q 1553 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1550 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1550)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 6 1 (meaning1518 q) (meaning1536 q) (meaning1550 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1536 = false ∨ valuation q 1550 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1551 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1551)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 6 2 (meaning1518 q) (meaning1537 q) (meaning1551 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1537 = false ∨ valuation q 1551 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1552 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1552)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 6 3 (meaning1518 q) (meaning1538 q) (meaning1552 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1538 = false ∨ valuation q 1552 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1553 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1553)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 6 4 (meaning1518 q) (meaning1539 q) (meaning1553 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1539 = false ∨ valuation q 1553 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1554 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1554)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 6 5 (meaning1518 q) (meaning1540 q) (meaning1554 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1540 = false ∨ valuation q 1554 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1552 = true := by
  have hs : count1544 q = (countLit q [-32, -34, -37, -38, -39, -42, -44]) + (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37, -38, -39, -42, -44]) (l₂ := [-46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1552)) (countLit q [-32, -34, -37, -38, -39, -42, -44]) (countLit q [-46, -47, -48, -50, -52, -54, -56, -58]) (count1544 q) 7 2 (meaning1519 q) (meaning1537 q) (meaning1552 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1537 = false ∨ valuation q 1552 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1570 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1570)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 2 10 (meaning1486 q) (meaning1553 q) (meaning1570 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1553 = false ∨ valuation q 1570 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1566 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1566)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 3 5 (meaning1487 q) (meaning1548 q) (meaning1566 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1548 = false ∨ valuation q 1566 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1567 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1567)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 3 6 (meaning1487 q) (meaning1549 q) (meaning1567 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1549 = false ∨ valuation q 1567 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1568 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1568)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 3 7 (meaning1487 q) (meaning1550 q) (meaning1568 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1550 = false ∨ valuation q 1568 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1569 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1569)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 3 8 (meaning1487 q) (meaning1551 q) (meaning1569 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1551 = false ∨ valuation q 1569 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1570 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1570)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 3 9 (meaning1487 q) (meaning1552 q) (meaning1570 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1552 = false ∨ valuation q 1570 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1571)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 3 10 (meaning1487 q) (meaning1553 q) (meaning1571 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1553 = false ∨ valuation q 1571 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1572)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 3 11 (meaning1487 q) (meaning1554 q) (meaning1572 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1554 = false ∨ valuation q 1572 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1566 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1566)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 4 4 (meaning1488 q) (meaning1547 q) (meaning1566 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1547 = false ∨ valuation q 1566 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1567 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1567)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 4 5 (meaning1488 q) (meaning1548 q) (meaning1567 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1548 = false ∨ valuation q 1567 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1568 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1568)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 4 6 (meaning1488 q) (meaning1549 q) (meaning1568 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1549 = false ∨ valuation q 1568 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1569 = true := by
  have hs : count1559 q = (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1569)) (countLit q [-3, -4, -6, -7, -9, -12, -15, -16, -18, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -34, -37, -38, -39, -42, -44, -46, -47, -48, -50, -52, -54, -56, -58]) (count1559 q) 4 7 (meaning1488 q) (meaning1550 q) (meaning1569 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1550 = false ∨ valuation q 1569 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E040.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112040
