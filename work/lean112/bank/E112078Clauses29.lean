import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1547 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1539)) (literal (valuationOf q) (1547)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 3 (meaning1539 q) (meaning1547 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1547 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1548 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1540)) (literal (valuationOf q) (1548)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 4 (meaning1540 q) (meaning1548 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1548 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1541)) (literal (valuationOf q) (1549)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 5 (meaning1541 q) (meaning1549 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1549 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1542)) (literal (valuationOf q) (1550)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 6 (meaning1542 q) (meaning1550 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1550 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1551 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1543)) (literal (valuationOf q) (1551)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 7 (meaning1543 q) (meaning1551 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1551 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1548 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1548)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 1 3 (meaning1514 q) (meaning1539 q) (meaning1548 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1539 = false ∨ valuation q 1548 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1549)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 1 4 (meaning1514 q) (meaning1540 q) (meaning1549 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1540 = false ∨ valuation q 1549 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1550)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 1 5 (meaning1514 q) (meaning1541 q) (meaning1550 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1541 = false ∨ valuation q 1550 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1551 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1551)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 1 6 (meaning1514 q) (meaning1542 q) (meaning1551 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1542 = false ∨ valuation q 1551 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1548 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1548)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 2 2 (meaning1515 q) (meaning1538 q) (meaning1548 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1538 = false ∨ valuation q 1548 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1549)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 2 3 (meaning1515 q) (meaning1539 q) (meaning1549 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1539 = false ∨ valuation q 1549 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1550)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 2 4 (meaning1515 q) (meaning1540 q) (meaning1550 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1540 = false ∨ valuation q 1550 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1551 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1551)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 2 5 (meaning1515 q) (meaning1541 q) (meaning1551 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1541 = false ∨ valuation q 1551 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1552 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1552)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 2 6 (meaning1515 q) (meaning1542 q) (meaning1552 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1542 = false ∨ valuation q 1552 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1553 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1553)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 2 7 (meaning1515 q) (meaning1543 q) (meaning1553 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1543 = false ∨ valuation q 1553 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1549)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 3 2 (meaning1516 q) (meaning1538 q) (meaning1549 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1538 = false ∨ valuation q 1549 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1550)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 3 3 (meaning1516 q) (meaning1539 q) (meaning1550 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1539 = false ∨ valuation q 1550 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1551 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1551)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 3 4 (meaning1516 q) (meaning1540 q) (meaning1551 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1540 = false ∨ valuation q 1551 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1552 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1552)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 3 5 (meaning1516 q) (meaning1541 q) (meaning1552 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1541 = false ∨ valuation q 1552 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1553)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 3 6 (meaning1516 q) (meaning1542 q) (meaning1553 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1542 = false ∨ valuation q 1553 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1554 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1554)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 3 7 (meaning1516 q) (meaning1543 q) (meaning1554 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1543 = false ∨ valuation q 1554 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1549)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 4 1 (meaning1517 q) (meaning1537 q) (meaning1549 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1537 = false ∨ valuation q 1549 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1550)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 4 2 (meaning1517 q) (meaning1538 q) (meaning1550 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1538 = false ∨ valuation q 1550 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1551 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1551)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 4 3 (meaning1517 q) (meaning1539 q) (meaning1551 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1539 = false ∨ valuation q 1551 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1552 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1552)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 4 4 (meaning1517 q) (meaning1540 q) (meaning1552 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1540 = false ∨ valuation q 1552 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1553 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1553)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 4 5 (meaning1517 q) (meaning1541 q) (meaning1553 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1541 = false ∨ valuation q 1553 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1554)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 4 6 (meaning1517 q) (meaning1542 q) (meaning1554 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1542 = false ∨ valuation q 1554 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1555 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1555)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 4 7 (meaning1517 q) (meaning1543 q) (meaning1555 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1543 = false ∨ valuation q 1555 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1550)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 5 1 (meaning1518 q) (meaning1537 q) (meaning1550 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1537 = false ∨ valuation q 1550 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1551 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1551)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 5 2 (meaning1518 q) (meaning1538 q) (meaning1551 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1538 = false ∨ valuation q 1551 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1552 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1552)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 5 3 (meaning1518 q) (meaning1539 q) (meaning1552 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1539 = false ∨ valuation q 1552 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1553 = true := by
  have hs : count1545 q = (countLit q [-27, -30, -32, -35, -38, -39, -42]) + (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -32, -35, -38, -39, -42]) (l₂ := [-46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1553)) (countLit q [-27, -30, -32, -35, -38, -39, -42]) (countLit q [-46, -47, -49, -52, -53, -55, -56, -57]) (count1545 q) 5 4 (meaning1518 q) (meaning1540 q) (meaning1553 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1540 = false ∨ valuation q 1553 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E078.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112078
