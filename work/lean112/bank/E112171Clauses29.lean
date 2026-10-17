import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1534 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1534)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 1 4 (meaning1503 q) (meaning1526 q) (meaning1534 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1526 = false ∨ valuation q 1534 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1532)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 2 1 (meaning1504 q) (meaning1523 q) (meaning1532 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1523 = false ∨ valuation q 1532 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1533 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1533)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 2 2 (meaning1504 q) (meaning1524 q) (meaning1533 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1524 = false ∨ valuation q 1533 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1534 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1534)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 2 3 (meaning1504 q) (meaning1525 q) (meaning1534 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1525 = false ∨ valuation q 1534 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1535 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1535)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 2 4 (meaning1504 q) (meaning1526 q) (meaning1535 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1526 = false ∨ valuation q 1535 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1536 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1536)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 2 5 (meaning1504 q) (meaning1527 q) (meaning1536 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1527 = false ∨ valuation q 1536 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_left (literal (valuationOf q) (1505)) (literal (valuationOf q) (1532)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 3 (meaning1505 q) (meaning1532 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1532 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1533 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1533)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 3 1 (meaning1505 q) (meaning1523 q) (meaning1533 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1523 = false ∨ valuation q 1533 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1534 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1534)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 3 2 (meaning1505 q) (meaning1524 q) (meaning1534 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1524 = false ∨ valuation q 1534 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1535 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1535)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 3 3 (meaning1505 q) (meaning1525 q) (meaning1535 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1525 = false ∨ valuation q 1535 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1536 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1536)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 3 4 (meaning1505 q) (meaning1526 q) (meaning1536 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1526 = false ∨ valuation q 1536 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1534 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1534)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 4 1 (meaning1506 q) (meaning1523 q) (meaning1534 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1523 = false ∨ valuation q 1534 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1535 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1535)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 4 2 (meaning1506 q) (meaning1524 q) (meaning1535 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1524 = false ∨ valuation q 1535 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1536 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1525)) (literal (valuationOf q) (1536)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 4 3 (meaning1506 q) (meaning1525 q) (meaning1536 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1525 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1525 = false ∨ valuation q 1536 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1535 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1523)) (literal (valuationOf q) (1535)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 5 1 (meaning1507 q) (meaning1523 q) (meaning1535 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1523 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1523 = false ∨ valuation q 1535 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1536 = true := by
  have hs : count1530 q = (countLit q [-58, -60, -63, -66, -68, -69, -71]) + (countLit q [-72, -76, -77, -78, -79, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -63, -66, -68, -69, -71]) (l₂ := [-72, -76, -77, -78, -79, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1536)) (countLit q [-58, -60, -63, -66, -68, -69, -71]) (countLit q [-72, -76, -77, -78, -79, -83, -85]) (count1530 q) 5 2 (meaning1507 q) (meaning1524 q) (meaning1536 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1524 = false ∨ valuation q 1536 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1544 = true := by
  have hs : count1544 q = (countLit q [-88]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1544)) (countLit q [-88]) (countLit q [-89]) (count1544 q) 1 (meaningNeg89 q) (meaning1544 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1544 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1544 = true := by
  have hs : count1544 q = (countLit q [-88]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1544)) (countLit q [-88]) (countLit q [-89]) (count1544 q) 1 (meaningNeg88 q) (meaning1544 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1544 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 89 = true ∨ valuationOf q 1545 = true := by
  have hs : count1544 q = (countLit q [-88]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (-89)) (literal (valuationOf q) (1545)) (countLit q [-88]) (countLit q [-89]) (count1544 q) 1 1 (meaningNeg88 q) (meaningNeg89 q) (meaning1545 q) hs
  change (! (valuationOf q 88)) = false ∨ (! (valuationOf q 89)) = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 89 = true ∨ valuation q 1545 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1546 = true := by
  have hs : count1546 q = (countLit q [-86]) + (countLit q [-88, -89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -89])
  have hm := merge_right (literal (valuationOf q) (1544)) (literal (valuationOf q) (1546)) (countLit q [-86]) (countLit q [-88, -89]) (count1546 q) 1 (meaning1544 q) (meaning1546 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1546 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1547 = true := by
  have hs : count1546 q = (countLit q [-86]) + (countLit q [-88, -89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -89])
  have hm := merge_right (literal (valuationOf q) (1545)) (literal (valuationOf q) (1547)) (countLit q [-86]) (countLit q [-88, -89]) (count1546 q) 2 (meaning1545 q) (meaning1547 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1547 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1546 = true := by
  have hs : count1546 q = (countLit q [-86]) + (countLit q [-88, -89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -89])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1546)) (countLit q [-86]) (countLit q [-88, -89]) (count1546 q) 1 (meaningNeg86 q) (meaning1546 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1546 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1544 = false ∨ valuationOf q 1547 = true := by
  have hs : count1546 q = (countLit q [-86]) + (countLit q [-88, -89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -89])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1547)) (countLit q [-86]) (countLit q [-88, -89]) (count1546 q) 1 1 (meaningNeg86 q) (meaning1544 q) (meaning1547 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1544 = false ∨ valuation q 1547 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1545 = false ∨ valuationOf q 1548 = true := by
  have hs : count1546 q = (countLit q [-86]) + (countLit q [-88, -89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -89])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1548)) (countLit q [-86]) (countLit q [-88, -89]) (count1546 q) 1 2 (meaningNeg86 q) (meaning1545 q) (meaning1548 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1545 = false ∨ valuation q 1548 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1549)) (countLit q [-93]) (countLit q [-94]) (count1549 q) 1 (meaningNeg94 q) (meaning1549 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1549 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1549)) (countLit q [-93]) (countLit q [-94]) (count1549 q) 1 (meaningNeg93 q) (meaning1549 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1549 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 94 = true ∨ valuationOf q 1550 = true := by
  have hs : count1549 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (1550)) (countLit q [-93]) (countLit q [-94]) (count1549 q) 1 1 (meaningNeg93 q) (meaningNeg94 q) (meaning1550 q) hs
  change (! (valuationOf q 93)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 94 = true ∨ valuation q 1550 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1551)) (countLit q [-95]) (countLit q [-96]) (count1551 q) 1 (meaningNeg96 q) (meaning1551 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1551 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1551)) (countLit q [-95]) (countLit q [-96]) (count1551 q) 1 (meaningNeg95 q) (meaning1551 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1551 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-93, -94]) + (countLit q [-95, -96]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-95, -96])
  have hm := merge_right (literal (valuationOf q) (1551)) (literal (valuationOf q) (1553)) (countLit q [-93, -94]) (countLit q [-95, -96]) (count1553 q) 1 (meaning1551 q) (meaning1553 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1553 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-93, -94]) + (countLit q [-95, -96]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-95, -96])
  have hm := merge_left (literal (valuationOf q) (1549)) (literal (valuationOf q) (1553)) (countLit q [-93, -94]) (countLit q [-95, -96]) (count1553 q) 1 (meaning1549 q) (meaning1553 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1553 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-93, -94]) + (countLit q [-95, -96]) := List.countP_append (p := literal q) (l₁ := [-93, -94]) (l₂ := [-95, -96])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1554)) (countLit q [-93, -94]) (countLit q [-95, -96]) (count1553 q) 1 1 (meaning1549 q) (meaning1551 q) (meaning1554 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1551 = false ∨ valuation q 1554 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E171.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112171
