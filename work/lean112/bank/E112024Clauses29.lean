import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 50 = true ∨ valuationOf q 1529 = true := by
  have hs : count1528 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (-50)) (literal (valuationOf q) (1529)) (countLit q [-47]) (countLit q [-50]) (count1528 q) 1 1 (meaningNeg47 q) (meaningNeg50 q) (meaning1529 q) hs
  change (! (valuationOf q 47)) = false ∨ (! (valuationOf q 50)) = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 50 = true ∨ valuation q 1529 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_right (literal (valuationOf q) (1528)) (literal (valuationOf q) (1530)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 1 (meaning1528 q) (meaning1530 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1530 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_right (literal (valuationOf q) (1529)) (literal (valuationOf q) (1531)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 2 (meaning1529 q) (meaning1531 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1531 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_left (literal (valuationOf q) (1526)) (literal (valuationOf q) (1530)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 1 (meaning1526 q) (meaning1530 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1530 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1531)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 1 1 (meaning1526 q) (meaning1528 q) (meaning1531 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1528 = false ∨ valuation q 1531 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1532)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 1 2 (meaning1526 q) (meaning1529 q) (meaning1532 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1529 = false ∨ valuation q 1532 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_left (literal (valuationOf q) (1527)) (literal (valuationOf q) (1531)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 2 (meaning1527 q) (meaning1531 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1531 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1532)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 2 1 (meaning1527 q) (meaning1528 q) (meaning1532 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1528 = false ∨ valuation q 1532 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1533 = true := by
  have hs : count1530 q = (countLit q [-43, -44]) + (countLit q [-47, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -44]) (l₂ := [-47, -50])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1533)) (countLit q [-43, -44]) (countLit q [-47, -50]) (count1530 q) 2 2 (meaning1527 q) (meaning1529 q) (meaning1533 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1529 = false ∨ valuation q 1533 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1534 = true := by
  have hs : count1534 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1534)) (countLit q [-53]) (countLit q [-54]) (count1534 q) 1 (meaningNeg54 q) (meaning1534 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1534 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1534 = true := by
  have hs : count1534 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1534)) (countLit q [-53]) (countLit q [-54]) (count1534 q) 1 (meaningNeg53 q) (meaning1534 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1534 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1535 = true := by
  have hs : count1534 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1535)) (countLit q [-53]) (countLit q [-54]) (count1534 q) 1 1 (meaningNeg53 q) (meaningNeg54 q) (meaning1535 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 54 = true ∨ valuation q 1535 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1536 = true := by
  have hs : count1536 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1536)) (countLit q [-55]) (countLit q [-56]) (count1536 q) 1 (meaningNeg56 q) (meaning1536 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1536 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1536 = true := by
  have hs : count1536 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1536)) (countLit q [-55]) (countLit q [-56]) (count1536 q) 1 (meaningNeg55 q) (meaning1536 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1536 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 56 = true ∨ valuationOf q 1537 = true := by
  have hs : count1536 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (1537)) (countLit q [-55]) (countLit q [-56]) (count1536 q) 1 1 (meaningNeg55 q) (meaningNeg56 q) (meaning1537 q) hs
  change (! (valuationOf q 55)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 56 = true ∨ valuation q 1537 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1538 = true := by
  have hs : count1538 q = (countLit q [-53, -54]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -56])
  have hm := merge_right (literal (valuationOf q) (1536)) (literal (valuationOf q) (1538)) (countLit q [-53, -54]) (countLit q [-55, -56]) (count1538 q) 1 (meaning1536 q) (meaning1538 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1538 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1539 = true := by
  have hs : count1538 q = (countLit q [-53, -54]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -56])
  have hm := merge_right (literal (valuationOf q) (1537)) (literal (valuationOf q) (1539)) (countLit q [-53, -54]) (countLit q [-55, -56]) (count1538 q) 2 (meaning1537 q) (meaning1539 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1539 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1538 = true := by
  have hs : count1538 q = (countLit q [-53, -54]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -56])
  have hm := merge_left (literal (valuationOf q) (1534)) (literal (valuationOf q) (1538)) (countLit q [-53, -54]) (countLit q [-55, -56]) (count1538 q) 1 (meaning1534 q) (meaning1538 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1538 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1539 = true := by
  have hs : count1538 q = (countLit q [-53, -54]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1539)) (countLit q [-53, -54]) (countLit q [-55, -56]) (count1538 q) 1 1 (meaning1534 q) (meaning1536 q) (meaning1539 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1536 = false ∨ valuation q 1539 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1540 = true := by
  have hs : count1538 q = (countLit q [-53, -54]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (1534)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1540)) (countLit q [-53, -54]) (countLit q [-55, -56]) (count1538 q) 1 2 (meaning1534 q) (meaning1537 q) (meaning1540 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1537 = false ∨ valuation q 1540 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1539 = true := by
  have hs : count1538 q = (countLit q [-53, -54]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -56])
  have hm := merge_left (literal (valuationOf q) (1535)) (literal (valuationOf q) (1539)) (countLit q [-53, -54]) (countLit q [-55, -56]) (count1538 q) 2 (meaning1535 q) (meaning1539 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1539 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1540 = true := by
  have hs : count1538 q = (countLit q [-53, -54]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1540)) (countLit q [-53, -54]) (countLit q [-55, -56]) (count1538 q) 2 1 (meaning1535 q) (meaning1536 q) (meaning1540 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1536 = false ∨ valuation q 1540 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1541 = true := by
  have hs : count1538 q = (countLit q [-53, -54]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1541)) (countLit q [-53, -54]) (countLit q [-55, -56]) (count1538 q) 2 2 (meaning1535 q) (meaning1537 q) (meaning1541 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1537 = false ∨ valuation q 1541 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1542 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_right (literal (valuationOf q) (1538)) (literal (valuationOf q) (1542)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 1 (meaning1538 q) (meaning1542 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1542 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1543 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_right (literal (valuationOf q) (1539)) (literal (valuationOf q) (1543)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 2 (meaning1539 q) (meaning1543 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1543 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1544 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_right (literal (valuationOf q) (1540)) (literal (valuationOf q) (1544)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 3 (meaning1540 q) (meaning1544 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1544 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1545 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_right (literal (valuationOf q) (1541)) (literal (valuationOf q) (1545)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 4 (meaning1541 q) (meaning1545 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1545 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1542 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_left (literal (valuationOf q) (1530)) (literal (valuationOf q) (1542)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 1 (meaning1530 q) (meaning1542 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1542 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1543 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1543)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 1 1 (meaning1530 q) (meaning1538 q) (meaning1543 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1538 = false ∨ valuation q 1543 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1544 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1544)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 1 2 (meaning1530 q) (meaning1539 q) (meaning1544 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1539 = false ∨ valuation q 1544 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1545 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1545)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 1 3 (meaning1530 q) (meaning1540 q) (meaning1545 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1540 = false ∨ valuation q 1545 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1546 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1546)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 1 4 (meaning1530 q) (meaning1541 q) (meaning1546 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1541 = false ∨ valuation q 1546 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E024.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112024
